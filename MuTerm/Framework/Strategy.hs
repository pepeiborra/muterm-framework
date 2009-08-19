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

-----------------------------------------------------------------------------
-- Functions
-----------------------------------------------------------------------------

-- Strategy combinators

-- | Or strategy combinator
(.|.) :: (MonadPlus m) => (t -> m a) -> (t -> m a) -> t -> m a
(f .|. g) m = f m `mplus` g m

-- | And strategy combinator
(.&.) :: (a -> Proof b) -> (b -> Proof c) -> a -> Proof c
(.&.) = (>=>)

infixl 5 .|.
infixl 5 .&.

-- | We apply the strategy recursively
fixSolver :: (a -> Proof a) -> a -> Proof a
fixSolver f x = let x' = f x in (x' >>= fixSolver f) -- x' `mplus` (x' >>= fixSolver f)