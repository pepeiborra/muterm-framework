{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}
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
import MuTerm.Framework.Proof (Proof)
import MuTerm.Framework.Problem

-----------------------------------------------------------------------------
-- Classes
-----------------------------------------------------------------------------


-- | Each processor is an instance of the class 'Processor'. The
-- output problem depends of the input problem
class Processor tag o d | tag o -> d where
  apply       :: MonadPlus mp => tag -> o -> Proof mp d
  applySearch :: MonadPlus mp => tag -> o -> [Proof mp d]

  apply       tag p = msum (applySearch tag p)
  applySearch tag p = [apply tag p]
