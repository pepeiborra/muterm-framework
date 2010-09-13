{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  MuTerm.Framework.GraphViz
-- Copyright   :  (c) muterm development team
-- License     :  see LICENSE
--
-- Maintainer  :  jiborra@dsic.upv.es
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

import Data.Foldable (Foldable(..), toList)
import Data.Traversable as T (Traversable(traverse))
import qualified Data.Traversable as T

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List hiding (unlines)
import Data.Maybe
import Data.Monoid
import Data.Traversable as T (Traversable, mapM, mapM)

import Data.Graph.Inductive as G hiding (node') 
import Data.Graph.Inductive.Tree
import Data.GraphViz.Attributes
import qualified Text.Dot
import Text.Dot hiding (node, edge, attribute)
import Text.PrettyPrint.HughesPJClass as Doc hiding (Style)

#ifdef DERIVE
import Data.DeriveTH
import Data.Derive.Functor
import Data.Derive.Traversable
#endif

import Prelude hiding (unlines)

import MuTerm.Framework.DotRep
import MuTerm.Framework.Proof
import MuTerm.Framework.Problem

instance (IsDPProblem typ, Pretty rules) => DotRep (Problem typ [rules]) where
  dot p = Text rep atts where
    atts = [ Shape BoxShape
           , Style (Stl Bold Nothing)
           , FontName "monospace"
           , FontSize 10
           , Margin (PVal (PointD 0.2 0.2))]
    rep = vcat
     [parens( text "PAIRS" $$
             nest 1 (vcat $ map pPrint (getP p)))
     ,parens( text "RULES" $$
             nest 1 (vcat $ map pPrint (getR p)))
     ]


g  = repG . dot
gs = repG . dotSimple

-- ----------------------------
-- GraphViz logs
-- ----------------------------

data DotProof = DotProof { showFailedPaths :: Bool }
dotProof = dotProof' DotProof{showFailedPaths=False}

dotProof' :: (IsMZero mp, Traversable mp, DotRep (SomeInfo info)) => DotProof -> Proof info mp a -> String
dotProof' DotProof{..} p = showDot $ do
                             attribute (Size (Point 100 100))
                             attribute (Compound True)
                             foldFree (\_ -> colorJoin False [textNode (text "?") []]) f
                              $ annotate (const False) isSuccess
                              $ p
 where
   f (Annotated done Success{..}) = colorJoin done [g problem, g procInfo, textNode (text "YES") [Color $ mkColor "#29431C"]]
   f (Annotated done Refuted{..}) = colorJoin done [g problem, g procInfo, textNode (text "NO")  [Color $ mkColor "#60233E"]]
   f (Annotated _ MDone{})        = mempty
   f (Annotated done DontKnow{..})= colorJoin done [g procInfo, textNode (text "Don't Know") []]
   f (Annotated done (MAnd p1 p2))= do
        (cme, node) <- cluster $ do
                 attribute (Color $ mkColor "#E56A90")
                 p1 ->> p2
        return (mkClusterNode cme <$> node)


   f (Annotated done And{subProblems=[p], ..}) = f (Annotated done Single{subProblem = p, ..})
   f (Annotated done And{..}) = do
        let trs = if (done || showFailedPaths) then g problem else return EmptyNode
        (cme, node) <- cluster $ do
                    attribute (Color $ mkColor "#E56A90")
                    colorJoin done [trs, g procInfo] ->> allPar subProblems
        return (mkClusterNode cme <$> node)

   f (Annotated done Single{..})
      | done || showFailedPaths = colorJoin done [g problem, g procInfo] ->> subProblem
      | otherwise               = colorJoin done [g procInfo] ->> subProblem

--   f (Annotated done (Search mk)) = colorJoin False [textNode (text " ") []]
   f (Annotated done (Search mk)) = do
        me <- node' [label $ text"?"] done
        T.mapM (return me ->>) mk
        return me

   g  = repG . dot
   gs = repG . dotSimple

colorJoin True  = foldMap (liftM (ParamJoin [Color $ mkColor "green"]))
colorJoin False = foldMap (liftM (ParamJoin [Color $ mkColor "red"]))

node' atts True  = ParamJoin [Color $ mkColor "green"] `liftM` node atts
node' atts False = ParamJoin [Color $ mkColor "red"]   `liftM` node atts

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
             | CompoundNode {headNode, tailNode :: DotNode}
             | ParNodes [DotNode]

  deriving Show

inId' DotNode{..} = inId
inId' ClusterNode{..} = inId
inId' (CompoundNode n1 _) = inId' n1
inId' (ParNodes nn) = error "inId' - unexpected: ParNodes"

outId' DotNode{..} = outId
outId' ClusterNode{..} = outId
outId' (CompoundNode _ n2) = outId' n2
outId' (ParNodes nn) = outId' (head nn)
--outId' (ParNodes nn) = error "outId' - unexpected: ParNodes"

mkClusterNode c DotNode{..} = ClusterNode{clusterId=c,..}
mkClusterNode c ClusterNode{..} = ClusterNode{clusterId=c,..}
mkClusterNode c (CompoundNode n1 n2) = ClusterNode{clusterId=c, inId = inId' n1, outId = outId' n2}
mkClusterNode c other = error ("mkClusterNode: " ++ show other)

instance Monoid (Dot DotNode) where
  mempty  = return EmptyNode
  mappend = (join.) . liftM2 (joinNodes [])

compoundNode (DotNode a b) (CompoundNode (DotNode c d) n3) = CompoundNode (DotNode a d) n3
compoundNode n1 n2 = CompoundNode n1 n2

joinNodes atts EmptyNode b = return b
joinNodes atts a EmptyNode = return a
joinNodes atts (DotNode a b) (DotNode c d)
            = do {edge b c atts; return (DotNode a d)}
joinNodes atts n1 n2@(ParNodes nn)
    = do {mapM_ (joinNodes atts n1) nn ; return $ CompoundNode n1 n2}
joinNodes atts n1@(DotNode a b) n2@(ClusterNode c d cId)
    = do {edge b c (LHead (show cId) : atts); return (compoundNode n1 n2)}
joinNodes atts n1@(ClusterNode a b cId) n2@(DotNode c d)
    = do {edge b c (LTail (show cId) : atts); return (compoundNode n1 n2)}
joinNodes atts n1@(ClusterNode a b cId) n2@(ClusterNode c d cId')
    = do {edge b c (LHead (show cId') : LTail (show cId) : atts); return (compoundNode n1 n2)}
joinNodes atts (CompoundNode n1 n2) n3
    = do {n2' <- joinNodes atts n2 n3; return (compoundNode n1 n2')}
joinNodes atts n1 (CompoundNode n2 n3)
    = do {n2' <- joinNodes atts n1 n2; return (compoundNode n2' n3)}
joinNodes _ n1 n2 = error ("joinNodes missing case for " ++ show n1 ++ " " ++ show n2)

parNodes EmptyNode b = b
parNodes a EmptyNode = a
parNodes (ParNodes n1) (ParNodes n2) = ParNodes (n1 ++ n2)
parNodes n1 (ParNodes n2) = ParNodes (n1 : n2)
parNodes (ParNodes n1) n2 = ParNodes (n1 ++ [n2])
parNodes  n1 n2 = ParNodes [n1, n2]

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

a ||| b = do
      ParamJoin c1 n1 <- a
      ParamJoin c2 n2 <- b
      return (ParamJoin (c1++c2) $ parNodes n1 n2)

allPar = Prelude.foldr (|||) mempty


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
repG Nodes{..} | null(G.nodes nodes) = error "repG: empty nodes graph"
repG Nodes{..} = do
  (c,(a,b)) <- cluster $ do
    maybe (return ()) (\(d,atts) -> mapM_ attribute (label d : atts)) legend
    mapM_ attribute attributes
    table <- Map.fromList `liftM` forM (labNodes nodes) (\(n,atts) -> do {n' <- node_ atts; return (n,n')})
    forM_ (labEdges nodes) $ \(n1,n2,atts) -> do
                   let Just n1' = Map.lookup n1 table
                       Just n2' = Map.lookup n2 table
                   edge n1' n2' atts
    case (Map.lookup incoming table, Map.lookup outgoing table) of
      (Just a, Just b) -> return (a,b)
      (Nothing,_)      -> error "invalid incoming node"
      (_,Nothing)      -> error "invalid outgoing node"

  return (ClusterNode a b c)

repG (Text t att) = textNode t att

-- -----------------
-- Derived instances
-- -----------------
#ifdef DERIVE
$(derive makeFunctor     ''DotGrF)
$(derive makeFoldable    ''DotGrF)
$(derive makeTraversable ''DotGrF)
#else
deriving instance Functor DotGrF
deriving instance Foldable DotGrF
deriving instance Traversable DotGrF
#endif