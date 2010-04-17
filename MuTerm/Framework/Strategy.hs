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


module MuTerm.Framework.Strategy (
   (.|.), (.||.), (.|||.),
   (.&.),
   final, FinalProcessor,
   try,
   simultaneously, parallelize,
   fixSolver, repeatSolver,
   lfp
  ) where

import MuTerm.Framework.Proof(Proof)

import Control.Applicative
import Control.Monad ((>=>), mplus, MonadPlus)
import Control.Monad.Free
import Control.Parallel.Strategies
import Data.Traversable (Traversable, traverse)
import MuTerm.Framework.Processor
import MuTerm.Framework.Proof

-----------------------------------------------------------------------------
-- Data
-----------------------------------------------------------------------------

-- | The final processor ends the strategy
data FinalProcessor  = FinalProcessor

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

-- | Try to apply a strategy and if it fails return the problem unmodified
try :: (Info info typ, Processor info processor typ typ, MonadPlus mp, Traversable mp) =>
       processor -> typ -> Proof info mp typ
try n x = case apply n x of
            Impure DontKnow{} -> return x
            Impure (Search m) -> Impure (Search (m `mplus` (return.return) x))
            res               -> res

lfp :: (Eq prob, Info info prob, Processor info processor prob prob, MonadPlus mp, Traversable mp) =>
       processor -> prob -> Proof info mp prob
lfp proc prob = do
  prob' <- try proc prob
  if prob == prob' then return prob' else lfp proc prob'

-- | If we have branches in the strategy that arrive to different kind
-- of problems, we have to close each branch with the same type
final _ = return FinalProcessor
