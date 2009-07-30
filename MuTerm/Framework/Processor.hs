{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
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

Processor (..)

) where

import MuTerm.Framework.Proof (Proof)

-----------------------------------------------------------------------------
-- Classes
-----------------------------------------------------------------------------

-- | Each processor is an instance of the class 'Processor'. The
-- output problem depends of the input problem and viceversa
class Processor tag o d | tag o -> d, tag d -> o where
  apply   :: tag -> o -> Proof d
