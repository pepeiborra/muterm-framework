{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  MuTerm.Framework.Strategy
-- Copyright   :  (c) muterm development team
-- License     :  see LICENSE
-- 
-- Maintainer  :  rgutierrez@dsic.upv.es
-- Stability   :  unstable
-- Portability :  non-portable 
--
-- This module manage the different strategies to solve a termination
-- problem
--
-----------------------------------------------------------------------------


module MuTerm.Framework.Strategy (
   (.|.), (.||.), (.|||.),
   (.&.),
   final, Final,
   try,
   simultaneously, parallelize,
   fixSolver, repeatSolver,
   lfp
  ) where

import MuTerm.Framework.Proof(Proof)

import Control.Applicative
import Control.DeepSeq
import Control.Monad ((>=>), mplus, MonadPlus)
import Control.Monad.Free
import Control.Parallel.Strategies
import Data.Traversable (Traversable, traverse)
import MuTerm.Framework.Problem
import MuTerm.Framework.Processor
import MuTerm.Framework.Proof
import GHC.Generics (Generic)
-----------------------------------------------------------------------------
-- Data
-----------------------------------------------------------------------------

-- | Final is just a type level tag to signal the end of a processor chain
data Final = Final deriving (Generic, Show)

-----------------------------------------------------------------------------
-- Functions
-----------------------------------------------------------------------------

-- Strategy combinators

-- | Or strategy combinator
(.|.) :: (MonadPlus m) => (t -> m a) -> (t -> m a) -> t -> m a
(f .|. g) m = f m `mplus` g m

-- | shallow parallel Or strategy combinator
(.||.) :: MonadPlus m => (t -> m a) -> (t -> m a) -> t -> m a
(f .||. g) m = uncurry mplus ((f m, g m)
                  `using`
               parPair rwhnf rwhnf)

-- | deep parallel Or strategy combinator
(.|||.) :: (NFData (Proof info m a), MonadPlus m) => (t -> Proof info m a) -> (t -> Proof info m a) -> t -> Proof info m a
(f .|||. g) m = uncurry mplus ((f m, g m)
                  `using`
               parPair rdeepseq rdeepseq)

-- | And strategy combinator
(.&.) :: Monad mp => (a -> Proof info mp b) -> (b -> Proof info mp c) -> a -> Proof info mp c
(.&.) = (>=>)

infixr 5 .|., .||., .|||.
infixr 5 .&.

parallelize :: (a -> Proof info mp a) -> a -> Proof info mp a
parallelize = (simultaneously .)

simultaneously :: Proof info mp a -> Proof info mp a
simultaneously = withStrategy parAnds

-- | Apply a strategy until a fixpoint is reached
fixSolver :: Monad mp => (a -> Proof info mp a) -> a -> Proof info mp a
fixSolver f x = let x' = f x in (x' >>= fixSolver f)

-- | Apply a strategy a bounded number of times
repeatSolver :: Monad mp => Int -> (a -> Proof info mp a) -> a -> Proof info mp a
repeatSolver max f = go max where
  go 0 x = return x
  go n x = let x' = f x in (x' >>= go (n-1))

isFailedLayer proof =
  case proof of
            Impure DontKnow{} -> True
            Impure (Search m) -> isMZero m
            _ -> False

-- | Try to apply a strategy and if it fails return the problem unmodified
try :: IsMZero mp => (a -> Proof info mp a) -> a -> Proof info mp a
try strat x = let res = strat x in if isFailedLayer res then return x else res

-- | Take the largest fixpoint of a strategy
lfp :: (IsMZero mp, Eq a) => (a -> Proof info mp a) -> a -> Proof info mp a
lfp strat prob = do
  let proof = strat prob
  if isFailedLayer proof then return prob else do
       prob' <- proof
       if prob == prob' then return prob else lfp strat prob'

-- | If we have branches in the strategy that arrive to different kind
-- of problems, we have to close each branch with the same type
final _ = return Final
