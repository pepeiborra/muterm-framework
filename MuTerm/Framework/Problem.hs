{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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

module MuTerm.Framework.Problem ( IsDPProblem(..), MkDPProblem(..) ) where


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
    getP, getR     :: DPProblem typ trs -> trs
    mapP, mapR     :: (trs -> trs) -> DPProblem typ trs -> DPProblem typ trs
    setR, setP     :: trs -> DPProblem typ trs -> DPProblem typ trs
    setR rr = mapR (const rr)
    setP rr = mapP (const rr)

class IsDPProblem typ => MkDPProblem typ trs where
    mkDPProblem    :: (rules ~ trs, pairs ~ trs) => typ -> rules -> pairs -> DPProblem typ trs
