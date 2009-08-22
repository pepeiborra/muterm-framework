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

  IsDPProblem (..)
, SomeProblem (..), someProblem
--,  RewProblem, CSRewProblem, TermProblem, CSTermProblem

-- * Exported functions


) where

import MuTerm.Framework.Ppr (Ppr (..))

import Data.Traversable
import Data.Monoid
import Text.XHtml (HTML(..))


-----------------------------------------------------------------------------
{-
-- Problems are modeled as a data family associated to the class IsDPProblem.
-- The motivation to use a type class is to keep the type of problems open.
-- The use of a data family to enclose the problem type is a win overall.
   * Benefits:
       - Separates the datatype of 'problem type' and the datatype carrying
         the tuple of problem components. This allows for very natural definitions,
         see e.g. Icap
       - Keeps the 'problem type' and the tuple of components semantically connected.
       - Allows us to define instances for DPProblems in general. E.g.
            > instance (IsDPProblem typ, HasRules t v trs) => HasRules t v (DPProblem typ trs) where
         as opposed to
            > instance (IsDPProblem p, HasRules t v trs) => HasRules t v (p trs) where
         which is more opaque to the GHC type checker
-}


class Functor (DPProblem typ) => IsDPProblem typ where
    data DPProblem typ :: * -> *
    getProblemType :: DPProblem typ trs -> typ
    mkDPProblem    :: (rules ~ trs, pairs ~ trs) => typ -> rules -> pairs -> DPProblem typ trs
    getP, getR     :: DPProblem typ trs -> trs
    mapP, mapR     :: (trs -> trs) -> DPProblem typ trs -> DPProblem typ trs
    setR, setP     :: trs -> DPProblem typ trs -> DPProblem typ trs
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
