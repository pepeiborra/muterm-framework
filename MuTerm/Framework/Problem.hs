{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  MuTerm.Framework.Problem
-- Copyright   :  (c) muterm development team
-- License     :  see LICENSE
-- 
-- Maintainer  :  rgutierrez@dsic.upv.es
-- Stability   :  unstable
-- Portability :  non-portable 
--
-- This module contains the different muterm problems with its type.
--
-----------------------------------------------------------------------------

module MuTerm.Framework.Problem (

-- * Exported data

  IsDPProblem (..), setP, setR
, SomeProblem (..), someProblem
--,  RewProblem, CSRewProblem, TermProblem, CSTermProblem

-- * Exported functions


) where

import MuTerm.Framework.Ppr (Ppr (..))

import Data.Traversable
import Data.Monoid
import Text.XHtml (HTML(..))


-----------------------------------------------------------------------------

class IsDPProblem typ where
    data DPProblem typ :: * -> *
    getProblemType :: DPProblem typ trs -> typ
    mkDPProblem    :: typ -> trs -> trs -> DPProblem typ trs
    getP, getR     :: DPProblem typ trs -> trs
    mapP, mapR     :: (trs -> trs) -> DPProblem typ trs -> DPProblem typ trs

setR, setP :: IsDPProblem typ => trs -> DPProblem typ trs -> DPProblem typ trs
setR rr = mapR (const rr)
setP rr = mapP (const rr)

-- | 'SomeProblem' hides the type of the problem
data SomeProblem where
    SomeProblem :: (HTML (DPProblem typ a), Ppr (DPProblem typ a)) => DPProblem typ a -> SomeProblem

-- | Pack the problem
someProblem :: (HTML (DPProblem typ a), Ppr (DPProblem  typ a)) => DPProblem typ a -> SomeProblem
someProblem = SomeProblem


instance Ppr  SomeProblem where ppr     (SomeProblem p) = ppr p
instance HTML SomeProblem where toHtml  (SomeProblem p) = toHtml p
