{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  MuTerm.Framework.GraphViz
-- Copyright   :  (c) muterm development team
-- License     :  see LICENSE
--
-- Maintainer  :  rgutierrez@dsic.upv.es
-- Stability   :  unstable
-- Portability :  non-portable
--
--
-----------------------------------------------------------------------------

module MuTerm.Framework.GraphViz where

import Control.Applicative
import Control.Arrow (first)
import Control.Monad
import Control.Monad.Free

import Data.DeriveTH
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..))
import Data.Traversable as T (Traversable(traverse))
import qualified Data.Traversable as T

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List hiding (unlines)
import Data.Maybe
import Data.Monoid
import Data.Traversable (Traversable)

import Data.Graph.Inductive as G
import Data.Graph.Inductive.Tree
import Data.GraphViz.Attributes
import qualified Text.Dot
import Text.Dot hiding (node, edge, attribute)

import Prelude hiding (unlines)

import MuTerm.Framework.DotRep
import MuTerm.Framework.Proof
import MuTerm.Framework.Problem

g  = repG . dot
gs = repG . dotSimple


-- ----------------------------
-- GraphViz logs
-- ----------------------------
sliceWorkDone = foldFree return (Impure . f) where
    f (Or  p pi pp) = (Or  p pi $ takeWhileAndOneMore (not . isSuccess) pp)
    f (And p pi pp) = (And p pi $ takeWhileAndOneMore isSuccess pp)
--    f (MPlusPar p1 p2) = if isSuccess p1 then Stage p1 else (MPlusPar p1 p2)  -- We use stage in lieu of return here
    f (MPlus    p1 p2) = if isSuccess p1 then Stage p1 else (MPlus    p1 p2)
    f (MAnd     p1 p2) = if not(isSuccess p1) then Stage p1 else (MAnd p1 p2)
    f x = x
    takeWhileAndOneMore _ []     = []
    takeWhileAndOneMore f (x:xs) = if f x then x : takeWhileAndOneMore f xs else [x]

data DotProof = DotProof { showFailedPaths :: Bool }
dotProof = dotProof' DotProof{showFailedPaths=False}

--dotProof' :: DotProof -> Proof a -> DotGr
dotProof' DotProof{..} p = showDot $ do
                             attribute (Size (Point 100 100))
                             attribute (Compound True)
                             foldFree (\_ -> colorJoin False [textNode "?" []]) f
                              $ annotate (const False) isSuccess
                              $ sliceWorkDone
                              $ p
 where
--   f (Annotated done Success{..}) = return (mdot problem >- mdot procInfo >- Text "YES" [mkColor "#29431C"])
   f (Annotated done Success{..}) = colorJoin done [g problem, g procInfo, textNode "YES" [mkColor "#29431C"]]
   f (Annotated done Fail{..})    = colorJoin done [g problem, g procInfo, textNode "NO"  [mkColor "#60233E"]]
   f (Annotated _ MZero{})        = mempty
   f (Annotated _ MDone{})        = mempty
   f (Annotated done DontKnow{..})= colorJoin done [g procInfo, textNode "Don't Know" []]
   f (Annotated done (MAnd p1 p2))= do
        (cme, node) <- cluster $ do
                 attribute (mkColor "#E56A90")
                 p1 ->> p2
        return (mkClusterNode cme <$> node)
--   f (Annotated done (MPlus p1 p2)) = colorJoin done [node [Shape PointShape, label ""], (p1 ||| p2)]
   f (Annotated done And{subProblems=[p], ..}) = f (Annotated done Single{subProblem = p, ..})
   f (Annotated done And{..}) = do
        let trs = if (done || showFailedPaths) then g problem else return EmptyNode
        (cme, node) <- cluster $ do
                    attribute (mkColor "#E56A90")
                    colorJoin done [trs, g procInfo] -- , allPar subProblems]
        return (mkClusterNode cme <$> node)

   f (Annotated done Single{..})
      | done || showFailedPaths = colorJoin done [g problem, g procInfo] ->> subProblem
      | otherwise               = colorJoin done [g procInfo] ->> subProblem
   f (Annotated _ (Stage p)) = p


colorJoin True  = foldMap (liftM (ParamJoin [mkColor "green"]))
colorJoin False = foldMap (liftM (ParamJoin [mkColor "red"]))

{-
{-
    f (Annotated done Or{..})   par
      | done || showFailedPaths = problemNode problem done par >>= proofnode done procInfo >>= \me -> forM_ subProblems ($ me) >> return me
      | otherwise = proofnode done procInfo par   >>= \me -> forM_ subProblems ($ me) >> return me
-}
--    problemLabel :: (Ord v, Ppr v, Ord id, Ppr id) => Problem id v -> (String, String)
    problemLabel p = ("label", pprTPDBdot p)

--    problemColor :: Problem id v -> (String, String)
--    problemAttrs :: (Ord v, Ppr v, Ord id, Show id) => Problem id v -> [(String,String)]
    problemAttrs p    = [problemLabel p, problemColor p, ("shape","box"), ("style","bold"),("fontname","monospace"),("fontsize","10"),("margin",".2,.2")]

    problemNode  (SomeProblem p) done par = childnode'(problemAttrs p) (doneEdge done) par

    proofnode' procInfo done par = childnode' [("label", show procInfo)] (doneEdge done) par

childnode' attrs edge_attrs (N par) = node (("URL","url"):attrs) >>= \n -> edge par n edge_attrs >> return (N n)
childnode' attrs edge_attrs (Cluster (cl,par)) = node (("URL","url"):attrs) >>= \n -> edge (getParentNode par) n (("ltail", show cl):edge_attrs) >> return (N n)

doneEdge True     = [("color", "green")]
doneEdge False    = [("color", "red")]


{-
    proofnode :: Bool -> SomeInfo -> Parent -> Dot Parent
    proofnode done (SomeInfo (DependencyGraph gr)) par | done || showFailedPaths = do
      (cl, nn) <- cluster (attribute ("shape", "ellipse") >> pprGraph gr [])
      case nn of
        []   -> return par
        me:_ -> do case par of
                     N n             -> edge n me ([("lhead", show cl)] ++ doneEdge done)
                     Cluster (cl',n) -> edge (getParentNode n) me [("ltail", show cl'), ("lhead", show cl)]
                   return (Cluster (cl, N me))

    proofnode done (SomeInfo (SCCGraph gr sccs)) par = do
      (cl, nn) <- cluster (
                    attribute ("shape", "ellipse") >>
                    pprGraph gr (zip sccs (cycle ["yellow","darkorange"
                                                 , "hotpink", "hotpink4", "purple", "brown","red","green"])))
      case (nn,par) of
        ([]  , _  )             -> return par
        (me:_, N n)             -> edge n me ([("lhead", show cl)] ++ doneEdge done) >> return (Cluster (cl, N me))
        (me:_, Cluster (cl',n)) -> edge (getParentNode n) me [("ltail", show cl'), ("lhead", show cl)] >> return (Cluster (cl, N me))


    proofnode done (SomeInfo (UsableGraph gr reachable)) par = do
      (cl, nn) <- cluster (attribute ("shape", "ellipse") >> (pprGraph gr [(reachable,"blue")]))
      case (nn,par) of
        ([]  , _  )             -> return par
        (me:_, N n)             -> edge n me ([("lhead", show cl)] ++ doneEdge done) >> return (Cluster (cl, N me))
        (me:_, Cluster (cl',n)) -> edge (getParentNode n) me ([("ltail", show cl'), ("lhead", show cl)] ++ doneEdge done) >> return (Cluster (cl, N me))
-}
-}

-- ----------------------------------------------------------------
-- dotgen constructors with a proper enumerated type for attributes
-- ----------------------------------------------------------------

node :: [Attribute] -> Dot DotNode
node att = do { n <- node_ att; return (DotNode n n)}

node_ = Text.Dot.node . map showA

edge :: NodeId -> NodeId -> [Attribute] -> Dot ()
edge n1 n2 = Text.Dot.edge n1 n2 . map showA

attribute :: Attribute -> Dot ()
attribute = Text.Dot.attribute . showA

showA att = (name,val)
   where  (name, _:val) = (takeWhile (/= '=') attRep, dropWhile (/= '=') attRep)
          attRep = show att

-- -------------------------------
-- Monoidal DotGen Graphs
-- -------------------------------

data DotNode = EmptyNode
             | DotNode  { inId , outId :: NodeId }
             | ClusterNode { inId , outId, clusterId :: NodeId }
             | ParNode { inIds, outIds :: [NodeId]}

mkClusterNode c (DotNode a b) = ClusterNode c a b

instance Monoid (Dot DotNode) where
  mempty  = return EmptyNode
  mappend = (join.) . liftM2 (joinNodes [])


joinNodes atts EmptyNode b = return b
joinNodes atts a EmptyNode = return a
joinNodes atts (DotNode a b) (ParNode aa bb)
    = do {mapM_ (\a -> edge b a atts) aa; return $ ParNode [a] bb}
joinNodes atts (DotNode a b) (ClusterNode c d cId)
    = do {edge b c (LHead (show cId) : LTail (show cId) : atts); return (DotNode a d)}
joinNodes atts (DotNode a b) (DotNode c d)
            = do {edge b c atts; return (DotNode a d)}

parNodes EmptyNode b = b
parNodes a EmptyNode = a
parNodes (DotNode a b) (DotNode c d) = ParNode [a,c] [b,d]

(|||) = liftM2 parNodes
allPar = Prelude.foldr (|||) (return EmptyNode)

textNode t att = do
  n <- node_ (label t : att)
  return (DotNode n n)


-- Joining DotNodes with customized edges

data ParamJoin a = ParamJoin {paramJoinAttributes::[Attribute], paramJoin :: a}

instance Functor ParamJoin where fmap f (ParamJoin atts a) = ParamJoin atts (f a)
instance Monoid (Dot (ParamJoin DotNode)) where
    mempty  = return emptyNode
    mappend a b = do
      ParamJoin c1 n1 <- a
      ParamJoin c2 n2 <- b
      (ParamJoin (c1++c2) `liftM` joinNodes (c1++c2) n1 n2)

emptyNode = ParamJoin [] EmptyNode

(->>) = mappend -- joinNodes []
--a ->> b = ParamJoin [] a `mappend` ParamJoin [] b


-- ---------------------------
-- Annotations on a free Monad
-- ---------------------------
data AnnotatedF n f a = Annotated {note::n, dropNote::f a}

instance Functor f => Functor (AnnotatedF n f) where fmap f (Annotated n x) = Annotated n (fmap f x)
instance Foldable f => Foldable (AnnotatedF n f) where foldMap f (Annotated _ x) = foldMap f x
instance Traversable f => Traversable (AnnotatedF n f) where traverse f (Annotated n x) = Annotated n <$> traverse f x

dropNotes = foldFree Pure (Impure . dropNote)
annotate :: Functor f => (a -> b) -> (Free f b -> n) -> Free f a -> Free (AnnotatedF n f) a
annotate p i = fmap fst . foldFree (\x -> Pure (x,p x))
               (\x -> Impure (Annotated (i $ Impure $ fmap (dropNotes . fmap snd) x) x))

-- ----------------------------------
-- Graphing fgl graphs
-- ----------------------------------

repG Nodes{..}    = do
  (c,(a,b)) <- cluster $ do
    mapM_ attribute attributes
    table <- Map.fromList `liftM` forM (labNodes nodes) (\(n,atts) -> do {n' <- node_ atts; return (n,n')})
    forM_ (labEdges nodes) $ \(n1,n2,atts) -> do
                   let Just n1' = Map.lookup n1 table
                       Just n2' = Map.lookup n2 table
                   edge n1' n2' atts
    let Just a = Map.lookup (head $ G.nodes nodes) table
        Just b = Map.lookup (last $ G.nodes nodes) table
    return (a, b)
  return (ClusterNode a b c)

repG (Text t att) = textNode t att

-- -----------------
-- Derived instances
-- -----------------
$(derive makeFunctor     ''DotGrF)
$(derive makeFoldable    ''DotGrF)
$(derive makeTraversable ''DotGrF)