{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances, FlexibleContexts #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  MuTerm.Framework.Processor
-- Copyright   :  (c) muterm development team
-- License     :  see LICENSE
-- 
-- Maintainer  :  rgutierrez@dsic.upv.es
-- Stability   :  unstable
-- Portability :  non-portable 
--
-- This module contains the processor definition.
--
-----------------------------------------------------------------------------

module MuTerm.Framework.Processor (

-- * Exported classes

Processor(..)

) where

import Control.Monad
import Data.Traversable (Traversable)
import MuTerm.Framework.Proof (Proof,Info)
import MuTerm.Framework.Problem

-----------------------------------------------------------------------------
-- Classes
-----------------------------------------------------------------------------


-- | Each processor is an instance of the class 'Processor'. The
-- output problem depends of the input problem
class Processor info tag o d | tag o -> info d where
  apply       :: (MonadPlus mp, Traversable mp, Info info o, Info info d) => tag -> o -> Proof info mp d
  applySearch :: (MonadPlus mp, Traversable mp, Info info o, Info info d) => tag -> o -> [Proof info mp d]

  apply       tag p = msum (applySearch tag p)
  applySearch tag p = [apply tag p]