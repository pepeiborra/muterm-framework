{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

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

ProofF(..), Proof

, SomeInfo (..), someInfo, Info, PrettyF
, IsMZero(..)

-- * Exported functions

, success, singleP, andP, dontKnow, refuted, mand, mprod
, isSuccess, runProof

-- * Evaluation strategies
, parAnds
, sliceProof, unsafeSliceProof
) where

import Control.Applicative
import Control.DeepSeq
import Control.Parallel.Strategies
import Control.Monad as M (MonadPlus(..), msum, guard, liftM, join, (>>=))
import Control.Monad.Free (MonadFree(..), Free (..), foldFree, evalFree, mapFree)
import Control.Applicative((<$>))
import Data.Foldable (Foldable(..), toList)
import Data.Suitable
import Data.TagBits
import Data.Traversable as T (Traversable(..), foldMapDefault)
import Data.Maybe (fromMaybe, isNothing, isJust, catMaybes, listToMaybe)
import Text.PrettyPrint.HughesPJClass

import MuTerm.Framework.Problem

import qualified Data.Foldable as F

import Prelude as P

-----------------------------------------------------------------------------
-- Proof Tree
-----------------------------------------------------------------------------

-- | Proof Tree constructors
data ProofF info (m :: * -> *) (k :: *) =
    And     {procInfo, problem :: !(SomeInfo info), subProblems::[k]}
  | Or      {procInfo, problem :: !(SomeInfo info), alternatives::m k}
  | Single  {procInfo, problem :: !(SomeInfo info), subProblem::k}
  | Success {procInfo, problem :: !(SomeInfo info)}
  | Refuted {procInfo, problem :: !(SomeInfo info)}
  | DontKnow{procInfo, problem :: !(SomeInfo info)}
  | Search !(m k)
  | MAnd  k k
  | MDone

-- | 'Proof' is a Free Monad. 'm' is the MonadPlus used for search
type Proof info m a = Free (ProofF info m) a

instance NFData a => NFData (ProofF info m a) where
  rnf (And _ _ pp) = rnf pp `seq` ()
  rnf Or{} = ()
  rnf (Single _ _ p) = rnf p `seq` ()
  rnf Success{} = ()
  rnf Refuted{} = ()
  rnf DontKnow{} = ()
  rnf Search{} = ()
  rnf (MAnd p1 p2) = rnf p1 `seq` rnf p2 `seq` ()
  rnf MDone = ()

-- ------------------------------
-- Parameterized super classes
-- ------------------------------
class    (Applicative f, Suitable f a) => Info f a
instance (Applicative f, Suitable f a) => Info f a

-- | Pretty printing info witness
newtype PrettyF a = PrettyF a deriving (Functor, Pretty)
instance Applicative PrettyF where
  pure = PrettyF
  PrettyF f <*> PrettyF a = PrettyF (f a)

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
    SomeInfo :: Suitable f p => f p -> SomeInfo f

instance Pretty (SomeInfo PrettyF) where
   pPrint (SomeInfo p) = withConstraintsOf p $ \PrettyDict -> pPrint p

-- Tuple instances

-- instance Pretty (SomeInfo (PrettyI, a)) where
--     pPrint (SomeInfo (p::p)) = withInfoOf p $ \(PrettyInfo :^: _) -> pPrint p

-- instance Pretty (SomeInfo (a,PrettyI)) where
--     pPrint (SomeInfo (p::p)) = withInfoOf p $ \((x::InfoConstraints a p) :^: PrettyInfo) -> pPrint p

-----------------------------------------------------------------------------
-- Instances
-----------------------------------------------------------------------------

instance Monad m => Functor (ProofF info m) where
  fmap f (And pi p kk)   = And pi p (fmap f kk)
  fmap f (Single pi p k) = Single pi p (f k)
  fmap _ (Success pi p)  = Success pi p
  fmap _ (Refuted pi p)  = Refuted pi p
  fmap _ (DontKnow pi p) = DontKnow pi p
  fmap f (Search mk)     = Search (liftM f mk)
  fmap f (MAnd k1 k2)    = MAnd (f k1) (f k2)
  fmap f MDone           = MDone

instance (Monad m, Traversable m) => Foldable (ProofF info m) where foldMap = T.foldMapDefault

instance (Monad m, Traversable m) => Traversable (ProofF info m) where
  traverse f (And pi p kk)   = And pi p <$> traverse f kk
  traverse f (Single pi p k) = Single pi p <$> f k
  traverse _ (Success pi p)  = pure $ Success pi p
  traverse _ (Refuted pi p)  = pure $ Refuted pi p
  traverse _ (DontKnow pi p) = pure $ DontKnow pi p
  traverse f (Search mk)     = Search <$> traverse f mk
  traverse f (MAnd k1 k2)    = MAnd <$> f k1 <*> f k2
  traverse f MDone           = pure MDone


-- MonadPlus

instance MonadPlus m => MonadPlus (Free (ProofF info m)) where
    mzero       = Impure (Search mzero)
    mplus !p1 p2 = Impure (Search (mplus (return p1) (return p2)))

-- Show
-----------------------------------------------------------------------------
-- Smart Constructors
-----------------------------------------------------------------------------

-- | Return a success node
success :: (Monad m, Info info p, Info info problem) => p -> problem -> Proof info m b
success pi p0 = Impure (Success (someInfo pi) (someProblem p0))

-- | Return a refuted node
refuted :: (Monad m, Info info p, Info info problem) => p -> problem -> Proof info m b
refuted pi p0 = Impure (Refuted (someInfo pi) (someProblem p0))

-- | Returns a don't know node
dontKnow :: (Monad m, Info info p, Info info problem) => p -> problem -> Proof info m b
dontKnow pi p0 = Impure (DontKnow (someInfo pi) (someProblem p0))

-- | Return a new single node
singleP :: (Monad m, Info info p, Info info problem) => p -> problem -> b -> Proof info m b
singleP pi p0 p = Impure (Single (someInfo pi) (someProblem p0) (return p))

-- | Return a list of nodes
andP :: (Monad m, Info info p, Info info problem) => p -> problem -> [b] -> Proof info m b
andP pi p0 [] = success pi p0
andP pi p0 pp = Impure (And (someInfo pi) (someProblem p0) (map return pp))

mand :: Monad m => Proof info m a -> Proof info m a -> Proof info m a
mand a b = Impure (MAnd a b)

mprod :: Monad m => [Proof info m a] -> Proof info m a
mprod = P.foldr mand (Impure MDone) where
  mand a (Impure MDone) = a
  mand a b = Impure (MAnd a b)

-- ---------
-- Functions
-- ---------

-- | Pack the proof information
someInfo :: (Info f p) => p -> SomeInfo f
someInfo = SomeInfo . pure

-- | Pack the problem
someProblem :: (Info f p) => p -> SomeInfo f
someProblem = SomeInfo . pure

-- | Obtain the solution, collecting the proof path in the way
evalSolF' :: (MonadPlus mp) => ProofF info mp (mp(Proof info t ())) -> mp (Proof info t ())
evalSolF' Refuted{..}    = return (Impure Refuted{..})
evalSolF' DontKnow{}     = mzero
evalSolF' MDone          = return (Impure MDone)
evalSolF' Success{..}    = return (Impure Success{..})
evalSolF' (Search mk)    = join mk
evalSolF' (And pi pb []) = return (Impure $ Success pi pb)
evalSolF' (And pi pb ll) = (Impure . And pi pb) `liftM` P.sequence ll
evalSolF' (Or  pi pb ll) = (Impure . Single pi pb) `liftM` join ll
evalSolF' (MAnd  p1 p2)  = p1 >>= \s1 -> p2 >>= \s2 ->
                           return (Impure $ MAnd s1 s2)
evalSolF' (Single pi pb p) = (Impure . Single pi pb) `liftM` p


class MonadPlus mp => IsMZero mp where isMZero :: mp a -> Bool
instance IsMZero []    where isMZero = null
instance IsMZero Maybe where isMZero = isNothing

-- | Evaluate if proof is success
isSuccess :: IsMZero mp => Proof info mp a -> Bool
isSuccess = not . isMZero . foldFree (const mzero) evalSolF'

-- | Apply the evaluation returning the relevant proof subtree
runProof :: MonadPlus mp => Proof info mp a -> mp (Proof info m ())
runProof = foldFree (const mzero) evalSolF'

-- Evaluation Strategies
-- Evaluate and branches in parallel
parAnds :: Strategy (Proof info m a)
parAnds (Pure p) = return (Pure p)
parAnds (Impure i) = liftM Impure (f i) where
   f (And    pi p pp)= And    pi p <$> parList parAnds pp
   f (Single pi p k) = Single pi p <$> parAnds k
   f (MAnd p1 p2)    = MAnd <$> rpar (p1 `using` parAnds) <*> rpar (p2 `using` parAnds)
   f it = return it

-- | Approximately slices a proof to keep only the evaluated branches.
--   Useful for things like displaying a failed proof.
sliceProof,unsafeSliceProof :: (Functor mp, Foldable mp, IsMZero mp) => Proof info mp a -> Proof info mp a
sliceProof = mapFree f where
    f (And p pi pp) = And p pi $ takeWhileAndOneMore isSuccess pp
    f (MAnd  p1 p2) = if not(isSuccess p1) then Search (return p1) else (MAnd p1 p2)
    f (Or  p pi pp) = Or  p pi $ takeWhileMP (not.isSuccess) pp
    f (Search m)    = Search   $ takeWhileMP (not.isSuccess) m
    f x = x

    takeWhileAndOneMore _ []     = []
    takeWhileAndOneMore f (x:xs) = if f x then x : takeWhileAndOneMore f xs else [x]

-- | Slices a proof to keep only the evaluated branches.
--   Uses the impure 'unsafeIsEvaluated' function from the tag-bits package to discern evaluated subtrees.
--   Regardless its name, 'unsafeSliceProof' is actually safe.
unsafeSliceProof = evalFree Pure (Impure . f) where
    f (And p pi pp) = let pp' = filterMP unsafeIsEvaluated pp in
                      And p pi $ map unsafeSliceProof $ takeWhileAndOneMore isSuccess pp'
    f (MAnd  p1 p2) = if not(isSuccess p1)
                       then Search (return $ sliceProof p1)
                      else (MAnd (sliceProof p1) (sliceProof p2))
    f (Or  p pi pp) = Or  p pi $ fmap unsafeSliceProof $ takeWhileMP (unsafeIsEvaluated .&. not.isSuccess) pp
    f (Search m)    = Search   $ fmap unsafeSliceProof $ takeWhileMP (unsafeIsEvaluated .&. not.isSuccess) m
    f x = x

    takeWhileAndOneMore _ []     = []
    takeWhileAndOneMore f (x:xs) = if f x then x : takeWhileAndOneMore f xs else [x]
    infixr 3 .&.
    f .&. g = \x -> f x && g x

filterMP, takeWhileMP :: (Foldable m, MonadPlus m) => (a -> Bool) -> m a -> m a
takeWhileMP p = F.foldr f mzero
  where
    f x acc  = if p x then return x `mplus` acc else mzero

filterMP p = F.foldr f mzero where f x acc = if p x then return x `mplus` acc else acc
