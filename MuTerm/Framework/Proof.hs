{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE KindSignatures, PolyKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric, DeriveDataTypeable #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  MuTerm.Framework.Proof
-- Copyright   :  (c) muterm development team
-- License     :  see LICENSE
-- 
-- Maintainer  :  rgutierrez@dsic.upv.es
-- Stability   :  unstable
-- Portability :  non-portable 
--
-- This module contains the proof functor.
--
-----------------------------------------------------------------------------

module MuTerm.Framework.Proof (

-- * Exported data

ProofF(..), Proof, search

, SomeInfo (..), someInfo, Info, PrettyF

-- * Exported functions

, success, aborted, singleP, andP, dontKnow, refuted, orElse, orElse1
, isSuccess, runProof

-- * Evaluation strategies
, parallelize, simultaneously, theAnds, theOrs
, unsafeSliceProof, simplifyProof
, pruneProof, pruneProofO
, pruneProofLazy, pruneProofLazyO
) where

import Control.Applicative
import Control.DeepSeq
import Control.Exception (catch, SomeException)
import Control.Parallel.Strategies
import Control.Monad as M (MonadPlus(..), liftM, join,msum)
import Control.Monad.Free (Free (..), foldFree, evalFree, mapFree, mapFreeM)
import Control.Monad.Free.Extras ()
import Control.Monad.Fix (fix)
import Control.Monad.Logic (MonadLogic(ifte))
import Control.Monad.State.Strict (StateT, MonadState(..), evalState)
import Control.Monad.Zip
import Data.Foldable (Foldable(..))
import Data.Maybe (fromMaybe)
import Data.Monoid ()
import Data.Suitable
import Data.TagBits
import Data.Traversable as T (Traversable(..), foldMapDefault)
import Data.Typeable
import Data.Maybe (isNothing)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJClass
import Prelude.Extras

import qualified Data.Foldable as F

import Prelude as P hiding (pi)
import GHC.Generics(Generic)

import Debug.Hoed.Observe
import Debug.Hoed.Observe.Instances

-----------------------------------------------------------------------------
-- Proof Tree
-----------------------------------------------------------------------------

-- | Proof Tree constructors
data ProofF info (k :: *) =
    And     {procInfo, problem :: !(SomeInfo info), subProblems::[k]}
  | Single  {procInfo, problem :: !(SomeInfo info), subProblem::k}
  | Success {procInfo, problem :: !(SomeInfo info)}
  | Refuted {procInfo, problem :: !(SomeInfo info)}
  | DontKnow{procInfo, problem :: !(SomeInfo info)}
  | Search ![k]
  | OrElse k k
  | Aborted String
  deriving (Generic,Generic1,Functor,Foldable,Traversable)

-- | 'Proof' is a Free Monad. 'm' is the MonadPlus used for search
type Proof info a = Free (ProofF info) a

instance (NFData a) => NFData (ProofF info a) 

instance (Observable(SomeInfo info)) => Observable1 (ProofF info)
instance (Observable(SomeInfo info), Observable a) => Observable(ProofF info a) where
  observers = observers1
  observer = observer1

problemInfoF :: ProofF info t -> Maybe (SomeInfo info)
problemInfoF Search{} = Nothing
problemInfoF OrElse{} = Nothing
problemInfoF (other)  = Just (problem other)

problemInfo (Impure x)  = problemInfoF x
problemInfo  Pure{}     = Nothing

procInfoF :: ProofF info t -> Maybe (SomeInfo info)
procInfoF (Search{}) = Nothing
procInfoF OrElse{}   = Nothing
procInfoF (other)    = Just (procInfo other)

-- | Smart constructor for Search
search :: [Proof info a] -> Proof info a
search [x] = x
search xx = Impure $ Search (xx >>= flatten) where
  flatten (Impure(Search yy)) = yy
  flatten other = return other

-- ------------------------------
-- Parameterized super classes
-- ------------------------------
type Info f a = (Applicative f, Suitable f a, Ord a, Ord1 f, Typeable a, Typeable f)

-- | Pretty printing info witness
newtype PrettyF a = PrettyF a deriving (Functor, Pretty)
instance Applicative PrettyF where
  pure = PrettyF
  PrettyF f <*> PrettyF a = PrettyF (f a)

instance Eq1 PrettyF where PrettyF x ==# PrettyF y = x == y
instance Ord1 PrettyF where compare1 (PrettyF x) (PrettyF y) = compare x y

data instance Constraints PrettyF a = Pretty a => PrettyDict
instance Pretty p => Suitable PrettyF p where constraints = PrettyDict

-- -- | Tuples of information witnesses
-- data instance InfoConstraints (i,j) a = (:^:) (InfoConstraints i a) (InfoConstraints j a)
-- instance (Info i a, Info j a) => Info (i,j) a where
--   constraints = constraints :^: constraints

-- ------------------------
-- Existential Wrappers
-- ------------------------

-- | 'SomeInfo' existentially wraps a value together with a dictionary for a set of constraints
data SomeInfo f where
    SomeInfo :: (Typeable f, Typeable p, Suitable f p, Ord p) => f p -> SomeInfo f


instance Eq1 info => Eq (SomeInfo info) where
  SomeInfo a == SomeInfo b =
    case gcast b of
      Nothing -> False
      Just b' ->  a ==# b'

instance Ord1 info => Ord (SomeInfo info) where
  compare (SomeInfo a) (SomeInfo b) =
    case gcast b of
      Nothing -> compare (typeOf a) (typeOf b)
      Just b' -> compare1 a b'

instance Pretty (SomeInfo PrettyF) where
   pPrint (SomeInfo p) = withConstraintsOf p $ \PrettyDict -> pPrint p

instance NFData (SomeInfo f) where rnf (SomeInfo x) = seq x ()

-- Tuple instances

-- instance Pretty (SomeInfo (PrettyI, a)) where
--     pPrint (SomeInfo (p::p)) = withInfoOf p $ \(PrettyInfo :^: _) -> pPrint p

-- instance Pretty (SomeInfo (a,PrettyI)) where
--     pPrint (SomeInfo (p::p)) = withInfoOf p $ \((x::InfoConstraints a p) :^: PrettyInfo) -> pPrint p

-----------------------------------------------------------------------------
-- Instances
-----------------------------------------------------------------------------

-- MonadPlus

instance Alternative(Free (ProofF info)) where
  empty = mzero
  (<|>) = mplus

instance MonadPlus (Free (ProofF info)) where
    mzero       = Impure (Search mzero)
    mplus (Impure(Search m1)) (Impure(Search m2)) = search $ mplus m1 m2
    mplus !p1 p2 = search [p1,p2]

-- Show
-----------------------------------------------------------------------------
-- Smart Constructors
-----------------------------------------------------------------------------

-- | Return a success node
success :: (Info info p, Info info problem) => p -> problem -> Proof info b
success pi p0 = Impure (Success (someInfo pi) (someProblem p0))

-- | Return a refuted node
refuted :: (Info info p, Info info problem) => p -> problem -> Proof info b
refuted pi p0 = Impure (Refuted (someInfo pi) (someProblem p0))

-- | Returns a don't know node
dontKnow :: (Info info p, Info info problem) => p -> problem -> Proof info b
dontKnow pi p0 = Impure (DontKnow (someInfo pi) (someProblem p0))

-- | Return a new single node
singleP :: (Info info p, Info info problem) => p -> problem -> b -> Proof info b
singleP pi p0 p = Impure (Single (someInfo pi) (someProblem p0) (return p))

-- | Return a list of nodes
andP :: (Info info p, Info info problem) => p -> problem -> [b] -> Proof info b
andP pi p0 [] = success pi p0
andP pi p0 pp = Impure (And (someInfo pi) (someProblem p0) (map return pp))

orElse a b = Impure (OrElse a b)
orElse1 a b x = Impure (OrElse (a x) (b x))

aborted msg = Impure (Aborted msg)

isAborted :: Proof info a -> Bool
isAborted(Impure (Aborted _)) = True
isAborted _ = False

-- ---------
-- Functions
-- ---------
xx `at` k = fromMaybe (error "at") (lookup k xx)

-- | Pack the proof information
someInfo :: (Typeable p, Info f p) => p -> SomeInfo f
someInfo = SomeInfo . pure

-- | Pack the problem
someProblem :: (Typeable p, Info f p) => p -> SomeInfo f
someProblem = SomeInfo . pure

-- | Obtain the solution, collecting the proof path in the way
evalSolF' :: (MonadLogic mp) => ProofF info (mp(Proof info ())) -> mp (Proof info ())
evalSolF' Refuted{..}    = return (Impure Refuted{..})
evalSolF' DontKnow{}     = mzero
evalSolF' Success{..}    = return (Impure Success{..})
evalSolF' (Search mk)    = msum mk
evalSolF' (And pi pb []) = return (Impure $ Success pi pb)
evalSolF' (And pi pb ll) = (Impure . And pi pb) `liftM` P.sequence ll
evalSolF' (Single pi pb p) = (Impure . Single pi pb) `liftM` p
evalSolF' (OrElse a b)   = ifte a return b
evalSolF' x@(Aborted msg) = mzero

-- | Evaluate if proof is success
isSuccess :: forall info a . Proof info a -> Bool
isSuccess proof = case runProof proof of [] -> False ; _ -> True

-- | Apply the evaluation returning the relevant proof subtree
runProof  :: (MonadLogic mp
             ) => Proof info a -> mp (Proof info ())
runProof = foldFree (const mzero) evalSolF'

-- | Approximately slices a proof to keep only the evaluated branches.
--   Useful for things like displaying a failed proof.
unsafeSliceProof :: Proof info a -> Proof info a

-- Eliminate intermediate steps that do not improve the problem
simplifyProof :: (Typeable info, Eq1 info) =>
                 Proof info a -> Proof info a
simplifyProof = removeEmpty

pruneProof :: ( Ord1 info
              , Observable (SomeInfo info), Observable1 Set.Set, Observable a) => Proof info a -> Proof info a
pruneProof = pruneProofO nilObserver
-- Eliminate duplicate subproofs
pruneProofO :: ( Ord1 info
               , Observable (SomeInfo info), Observable1 Set.Set, Observable a
               ) => Observer -> Proof info a -> Proof info a
pruneProofO (O o oo) = (`evalState` Set.empty) . mapFreeM (oo "f" f) where
  f (O o oo) x@Success{}  = return x
  f (O o oo) x@DontKnow{} = return x
  f (O o oo) x@Refuted{}  = return x
  f (O o oo) x@And{}      = return x
--  f (O o oo) x@Single{}   = return x -- this case shouldn't be here, but..
  f (O o oo) x | Just pi <- problemInfoF x
               , Just procI <- procInfoF x
               = do
    seen <- get
    if o "member" Set.member (pi, procI) seen
       then return $ Search mzero
       else do
         put (Set.insert (pi,procI) seen)
         return x
  f _ x = return x

{- Circular version of pruneProof, as unfortunately the monadic one makes the tree strict and therefore is useless for our purposes.
   Here we make use of circularity to compute a map from (problemInfo, procInfo) to a position in the tree,
   that we then use to remove duplicates from the tree.
   But instead of doing it in two passes, we do it in the same one, which means we don't have to force the entire tree.
 -}


pruneProofLazy :: ( Eq1 info
                  , Observable(SomeInfo info), Observable a
                  ) => Free (ProofF info) a
                    -> Free (ProofF info) a
pruneProofLazy x = pruneProofLazyO nilObserver x

pruneProofLazyO :: ( Eq1 info
                   , Observable(SomeInfo info), Observable a
                   ) => Observer
                     -> Free (ProofF info) a
                     -> Free (ProofF info) a
pruneProofLazyO (O o oo) x =
  let (seen, res) = foldFree (\v -> ([], Pure v)) (oo "f" f seen) x in res
 where
  f _ _    (Success  pi p)                        = ([], Impure(Success  pi p))
  f _ _    (DontKnow pi p)                        = ([], Impure(DontKnow pi p))
  f _ _    (Refuted  pi p)                        = ([], Impure(Refuted  pi p))

  f _ seen (And      pi p (unzip -> (seens,xx)))  = ( ((pi,p), Impure(And pi p xx)) : concat seens
                                                    , seen `at` (pi,p))
  f _ seen (Single   pi p (seens,it))             = ( ((pi,p), Impure(Single pi p it)) : seens
                                                    , seen `at` (pi,p))
  f _ _    (Search   (munzip -> (seens, xx)))     = ( concat(seens), Impure(Search xx))
  f _ _    (OrElse (seens1, x1) (seens2, x2))     = ( seens1 ++ seens2, Impure(OrElse x1 x2 ))

  xx `at` k = fromMaybe (error "at") (lookup k xx)

removeEmpty :: Proof info a -> Proof info a
removeEmpty =  search . foldFree (return . Pure) f where
  f (Search k) =
    let filtered = filter (not.null) k in
    case F.toList filtered of
      []  -> mzero
      [x] -> x
      _   -> return $ search $ join $ filtered
  f (OrElse a b)
    | null a = b
    | null b = a
    | otherwise = orElse <$> a <*> b
  f other = fmap Impure $ T.sequence other

removeIdem x = foldFree (\v _ -> Pure v) f x (problemInfo x)
 where
  f(And _ pi [subp]) parent
    | Just pi == parent {-|| isNothing parent-} = subp parent
  f(And p pi pp) _parent = Impure $ And p pi (map ($ Just pi) pp)
  f(Single p pi k) parent
    | Just pi == parent {-|| isNothing parent-} = k parent
    | otherwise = Impure $ Single p pi (k $ Just pi)
  f(Search k) parent = search (liftM ($ parent) k)
  f(DontKnow p pi) _ = Impure $ DontKnow p pi
  f(Success p pi)  _ = Impure $ Success p pi
  f(Refuted p pi)  _ = Impure $ Refuted p pi
  f(OrElse p1 p2) pa = Impure $ OrElse (p1 pa) (p2 pa)
  f(Aborted msg)   _ = Impure $ Aborted msg
  
-- | Slices a proof to keep only the evaluated branches.
--   Uses the impure 'unsafeIsEvaluated' function from the tag-bits package to discern evaluated subtrees.
--   Regardless its name, 'unsafeSliceProof' is actually safe.
unsafeSliceProof x
  | not (unsafeIsEvaluated x) = aborted "..."
  | Pure _ <- x = x
  | Impure y <- x = Impure (f y)
  where
    f x | not (unsafeIsEvaluated x) = Search mzero
    f (And p pi pp) = And p pi $ map unsafeSliceProof pp
    f (Search m)    = Search   $ fmap unsafeSliceProof m
    f (Single proof p p') = Single proof p $ unsafeSliceProof p'
    f (OrElse p1 p2) = OrElse (unsafeSliceProof p1) (unsafeSliceProof p2)
    f x = x

    isEvaluated = unsafeIsEvaluated

-- * Parallel Evaluation
parallelize :: Strategy(Proof info a)
parallelize = simultaneously ( theOrs . theAnds )

simultaneously :: Functorial(ProofStrategyPart info a) -> Strategy(Proof info a)
simultaneously s = foldFree (return.return) (fix ( s . seqF )) 

type Functorial a = a -> a
type ProofStrategyPart info a = ProofF info (Eval (Proof info a)) -> Eval (Proof info a)

theAnds, theOrs, seqF:: Functorial (ProofStrategyPart info a)

theAnds k (And pi pb pp) = Impure . And pi pb    <$> parList   rseq (map runEval pp)
theAnds k other = k other

theOrs  k (Search m)     = Impure . Search         <$> parTraversable rseq (runEval <$> m)
theOrs  k (OrElse a b)   = Impure . uncurry OrElse <$> parTuple2 rseq rseq (runEval a, runEval b)
theOrs  k other          = k other

seqF k (Search m) = do
  search' <- return $! Search $ runEval <$> m
  return (Impure search')
seqF k (OrElse a b) = return $ Impure $ OrElse (runEval a) (runEval b)
seqF k (And pi pb pp) = do
  s' <- return $! And pi pb $ fmap runEval pp
  return (Impure s')
seqF k (Single pi pb p) = Impure . Single pi pb <$> p
seqF k other = do
  -- Avoid sequence as it would introduce too much strictness
  -- forcing all the contents before wrapping in the Impure
  x <- return $! fmap runEval other
  return (Impure x)

-- parOrF  s (Or pi pb pp)  = Or pi pb <$> parList s pp
    
