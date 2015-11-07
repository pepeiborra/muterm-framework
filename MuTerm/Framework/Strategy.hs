{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE BangPatterns #-}
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
   try, orElse,
   simultaneously, parallelize,
   foreverTry, repeatSolver,
   fix, fixBounded
  ) where

import MuTerm.Framework.Proof(Proof)

import Control.Applicative
import Control.DeepSeq
import Control.Monad ((>=>), mplus, MonadPlus)
import Control.Monad.Free
import Control.Parallel.Strategies
import Data.Foldable (Foldable, toList)
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
(.|||.) :: (NFData (Proof info a)) => (t -> Proof info a) -> (t -> Proof info a) -> t -> Proof info a
(f .|||. g) m = uncurry mplus ((f m, g m)
                  `using`
               parPair rdeepseq rdeepseq)

-- | And strategy combinator
(.&.) :: (a -> Proof info b) -> (b -> Proof info c) -> a -> Proof info c
(.&.) = (>=>)

infixr 5 .|., .||., .|||.
infixr 5 .&.

-- | Apply a strategy until it fails
foreverTry :: (a -> Proof info a) -> a -> Proof info a
foreverTry f x = f x >>= try (foreverTry f)

-- | Apply a strategy a bounded number of times
repeatSolver ::Int -> (a -> Proof info a) -> a -> Proof info a
repeatSolver max f = go max where
  go 0 x = return x
  go n x = let x' = f x in (x' >>= go (n-1))

try strat p = strat p `orElse` return p

-- | Take the fixpoint of a strategy (bounded).
fixBounded :: (Eq a) => Int -> (a -> Proof info a) -> a -> Proof info a
fixBounded n strat = try (go n) where
  go  0 prob = return prob
  go !n prob = do
       prob' <- strat prob
       if prob == prob' then return prob else go (n-1) prob'

-- | Take the fixpoint of a strategy
fix :: (Eq a) => (a -> Proof info a) -> a -> Proof info a
fix x = fixBounded (-1) x


-- | If we have branches in the strategy that arrive to different kind
-- of problems, we have to close each branch with the same type
final _ = return Final
