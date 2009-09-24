{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
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

ProofF(..), Proof, Solution (..)

, Info(..), withInfoOf, PrettyInfo
, SomeProblem(..), someProblem
, SomeInfo (..), someInfo
, IsMZero(..)

-- * Exported functions
, success, singleP, andP, dontKnow, failP, mand, mprod
, isSuccess, runProof -- , runProof, runProofSol', runProofByStages

) where


import Control.Monad as M (MonadPlus(..), msum, liftM, join, (>>=))
import Control.Monad.Free (MonadFree(..), Free (..), foldFree)
import Control.Applicative((<$>))
import Data.Maybe (fromMaybe, isNothing, isJust, catMaybes, listToMaybe)
import System.IO.Unsafe (unsafePerformIO)
import Text.PrettyPrint.HughesPJClass


import Control.Applicative
import Data.DeriveTH
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), foldMapDefault)

import MuTerm.Framework.Problem


import Prelude as P

-----------------------------------------------------------------------------
-- Proof Tree
-----------------------------------------------------------------------------

-- | Proof Tree constructors
data ProofF info (m :: * -> *) (k :: *) =
    And     {procInfo :: !(SomeInfo info), problem :: !(SomeProblem info), subProblems::[k]}
  | Or      {procInfo :: !(SomeInfo info), problem :: !(SomeProblem info), alternatives::m k}
  | Single  {procInfo :: !(SomeInfo info), problem :: !(SomeProblem info), subProblem::k}
  | Success {procInfo :: !(SomeInfo info), problem :: !(SomeProblem info)}
  | Fail    {procInfo :: !(SomeInfo info), problem :: !(SomeProblem info)}
  | DontKnow{procInfo :: !(SomeInfo info), problem :: !(SomeProblem info)}
  | Search (m k)
  | MAnd  k k
  | MDone

-- -------------------
-- Sebastian's monad
-- -------------------
data ProofS m a =
    PureS a
  | AndS  [ProofS m a]
  | LazyS (m (ProofS m a))

type ProofListT a = [ProofS [] a]

instance Monad m => Monad (ProofS m) where
  return = PureS
  PureS a >>= f = f a
  AndS aa >>= f = AndS (P.map (>>=f) aa)
  LazyS a >>= f = LazyS (liftM (>>= f) a)

runProofS :: MonadPlus m => ProofS m a -> m (ProofS t a)
runProofS = foldProofS (return . PureS) (liftM AndS . P.sequence) join

foldProofS :: (a -> b) -> ([b] -> b) -> (m b -> b) -> ProofS m a -> b
foldProofS = undefined


-- | 'Proof' is a Free Monad. 'm' is the MonadPlus used for search
type Proof info m a = Free (ProofF info m) a
{-
f :: Proof a -> IO (Proof a)
f = lift . foldFree g where
  g (Stage k) = k >>= id
  g (t :: ProofF (IO (Proof a))) = fmap Impure (sequence t)
-}



-- ------------------
-- Solution datatype
-- ------------------
-- | Solution is the result of the evaluation
data Solution a = YES a
                | NO  a
                | MAYBE

isNo NO{} = True; isNo _ = False
isMaybe MAYBE{} = True; isMaybe _ = False
isYes YES{} = True; isYes _ = False

catYes []               = []
catYes ((YES sol):sols) = sol:(catYes sols)
catYes (_:sols)         = catYes sols

mapYes f (YES x) = YES x
mapYes _ x       = x

-- | Isomorphic to the Maybe monad (return == YES)
instance Monad Solution where
  return = YES
  YES a >>= f = f a
  NO  a >>= f = f a
  MAYBE >>= _ = MAYBE

-- | The MonadPlus instance elegantly enforces the priority of NO over YES
instance MonadPlus Solution where
  mzero = MAYBE
  YES a `mplus` NO b = NO b
  YES a `mplus` _    = YES a
  NO  a `mplus` _    = NO  a
  MAYBE `mplus` b    = b

-- ------------------------------
-- Parameterized super classes
-- ------------------------------

-- Instance witnesses
class Info info p where
  data InfoConstraints info p
  constraints :: InfoConstraints info p

withInfoOf :: Info info a => a -> (InfoConstraints info a -> b) -> b
withInfoOf _ f = f constraints


-- | Pretty printing info witness
data PrettyInfo
instance Pretty p => Info PrettyInfo p where
  data InfoConstraints PrettyInfo p = Pretty p => PrettyInfo
  constraints = PrettyInfo

-- ------------------------
-- Existential Wrappers
-- ------------------------

-- | 'SomeInfo' hides the type of the proccesor info
data SomeInfo info where
    SomeInfo :: Info info p => p -> SomeInfo info

-- | 'SomeProblem' hides the type of the problem
data SomeProblem info where
    SomeProblem :: Info info p => p -> SomeProblem info

instance Show (SomeProblem info) where
  show _ = "SomeProblem"

instance Pretty (SomeInfo PrettyInfo) where
    pPrint (SomeInfo p) = withInfoOf p $ \PrettyInfo -> pPrint p

instance Pretty (SomeProblem PrettyInfo) where
    pPrint (SomeProblem p) = withInfoOf p $ \PrettyInfo -> pPrint p

-----------------------------------------------------------------------------
-- Instances
-----------------------------------------------------------------------------
$(derive (makeFunctorN 1)     ''Solution)

instance Monad m => Functor (ProofF info m) where
  fmap f (And pi p kk)   = And pi p (fmap f kk)
  fmap f (Single pi p k) = Single pi p (f k)
  fmap _ (Success pi p)  = Success pi p
  fmap _ (Fail pi p)     = Fail pi p
  fmap _ (DontKnow pi p) = DontKnow pi p
  fmap f (Search mk)     = Search (liftM f mk)
  fmap f (MAnd k1 k2)    = MAnd (f k1) (f k2)
  fmap f MDone           = MDone

instance (Monad m, Traversable m) => Foldable (ProofF info m) where foldMap = T.foldMapDefault

instance (Monad m, Traversable m) => Traversable (ProofF info m) where
  traverse f (And pi p kk)   = And pi p <$> traverse f kk
  traverse f (Single pi p k) = Single pi p <$> f k
  traverse _ (Success pi p)  = pure $ Success pi p
  traverse _ (Fail pi p)     = pure $ Fail pi p
  traverse _ (DontKnow pi p) = pure $ DontKnow pi p
  traverse f (Search mk)     = Search <$> traverse f mk
  traverse f (MAnd k1 k2)    = MAnd <$> f k1 <*> f k2
  traverse f MDone           = pure MDone


-- MonadPlus

instance MonadPlus m => MonadPlus (Free (ProofF info m)) where
    mzero       = Impure (Search mzero)
    mplus p1 p2 = Impure (Search (mplus (return p1) (return p2)))

-- Show
{-
instance Show (SomeInfo info) where
    show (SomeInfo p) = show (pPrint p)
-}
-----------------------------------------------------------------------------
-- Smart Constructors
-----------------------------------------------------------------------------

-- | Return a success node
success :: (Monad m, Info info p, Info info problem) => p -> problem -> Proof info m b
success pi p0 = Impure (Success (someInfo pi) (someProblem p0))

-- | Return a fail node
failP :: (Monad m, Info info p, Info info problem) => p -> problem -> Proof info m b
failP pi p0 = Impure (Fail (someInfo pi) (someProblem p0))

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

mand :: Monad m => a -> a -> Proof info m a
mand a b = Impure (MAnd (return a) (return b))

mprod :: Monad m => [a] -> Proof info m a
mprod = P.foldr mand (Impure MDone) . map return where
  mand a (Impure MDone) = a
  mand a b = Impure (MAnd a b)

-- ---------
-- Functions
-- ---------

-- | Pack the proof information
someInfo :: Info info p => p -> SomeInfo info
someInfo = SomeInfo

-- | Pack the problem
someProblem :: Info info p => p -> SomeProblem info
someProblem = SomeProblem

-- | Obtain the solution, collecting the proof path in the way
evalSolF' :: (MonadPlus mp) => ProofF info mp (mp(Proof info t ())) -> mp (Proof info t ())
evalSolF' Fail{..}       = mzero -- return (wrap Fail{..})
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
