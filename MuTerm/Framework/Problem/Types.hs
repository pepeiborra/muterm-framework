{-# LANGUAGE DeriveGeneric #-}

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
-- This module contains standard problem types
--
-----------------------------------------------------------------------------

module MuTerm.Framework.Problem.Types where

import Control.DeepSeq
import GHC.Generics

data Rewriting  = Rewriting  deriving (Eq, Ord, Show, Generic)
data IRewriting = IRewriting deriving (Eq, Ord, Show, Generic)

instance NFData Rewriting
instance NFData IRewriting
