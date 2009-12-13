
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

data Rewriting  = Rewriting  deriving (Eq, Ord, Show)
data IRewriting = IRewriting deriving (Eq, Ord, Show)

instance NFData Rewriting
instance NFData IRewriting
