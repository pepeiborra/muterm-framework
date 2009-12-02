{-# LANGUAGE FlexibleContexts #-}
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

module MuTerm.Framework.Strategy where

import MuTerm.Framework.Proof(Proof)

import Control.Monad ((>=>), mplus, MonadPlus)
import Control.Monad.Free
import MuTerm.Framework.Proof

-----------------------------------------------------------------------------
-- Functions
-----------------------------------------------------------------------------

-- Strategy combinators

-- | Or strategy combinator
(.|.) :: (MonadPlus m) => (t -> m a) -> (t -> m a) -> t -> m a
(f .|. g) m = f m `mplus` g m

-- | And strategy combinator
(.&.) :: Monad mp => (a -> Proof info mp b) -> (b -> Proof info mp c) -> a -> Proof info mp c
(.&.) = (>=>)

infixl 5 .|.
infixl 5 .&.

-- | Apply a strategy until a fixpoint is reached
fixSolver :: Monad mp => (a -> Proof info mp a) -> a -> Proof info mp a
fixSolver f x = let x' = f x in (x' >>= fixSolver f)

-- | Apply a strategy a bounded number of times
repeatSolver :: Monad mp => Int -> (a -> Proof info mp a) -> a -> Proof info mp a
repeatSolver max f = go max where
  go 0 x = return x
  go n x = let x' = f x in (x' >>= go (n-1))

-- | Try to apply a strategy and if it fails return the problem unmodified
try :: MonadPlus mp => (a -> Proof info mp a) -> a -> Proof info mp a
try f x = case f x of
            Impure DontKnow{} -> return x
            Impure (Search m) -> Impure (Search (m `mplus` (return.return) x))
            res               -> res

-- | If we have branches in the strategy that arrive to different kind
-- of problems, we have to close each branch with the same type
final _ = return ()
