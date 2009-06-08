{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Framework.Processor
-- Copyright   :  (c) muterm development team
-- License     :  see LICENSE
-- 
-- Maintainer  :  jiborra@dsic.upv.es
-- Stability   :  unstable
-- Portability :  non-portable 
--
-- This module contains the processor definition.
--
-----------------------------------------------------------------------------

module Framework.Processor (

-- * Exported classes

Processor (..)

) where

import Framework.Problem (ProblemF (..), RProblem, DPProblem)
import Framework.Proof (ProofF (..), Proof, success, singleP, andP, dontKnow, ProofInfo(..))

-- | Each processor is an instance of the class 'Processor'. The
-- output problem depends of the input problem and viceversa
class Processor tag o d | tag o -> d, tag d -> o where
  apply   :: tag -> o -> Proof d

{--
instance Processor SCCProcessor (Problem CSDP) (Problem CSDP) where
  apply = ...


instance Processor SCCProcessor (Problem OSDP) (Problem OSDP) where
  apply = ...
--}