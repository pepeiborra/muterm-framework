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

module MuTerm.Framework.Problem ( 

IsProblem(..), IsDPProblem(..), MkDPProblem(..) 

) where


{-----------------------------------------------------------------------------
-- Problems are modeled as a data family associated to the class
-- IsProblem.  The motivation to use a type class is to keep the type
-- of problems open and modular. The use of a data family to enclose
-- the problem type is a win overall.

   * Benefits:
       - Separates the datatype of 'problem type' and the datatype carrying
         the tuple of problem components. This allows for very natural definitions,
         see e.g. Icap
       - Keeps the 'problem type' and the tuple of components semantically connected.
-----------------------------------------------------------------------------}

class Functor (Problem typ) => IsProblem typ where
    data Problem typ :: * -> *
    getProblemType :: Problem typ trs -> typ
    getR     :: Problem typ trs -> trs
    mapR     :: (trs -> trs) -> Problem typ trs -> Problem typ trs
    setR     :: trs -> Problem typ trs -> Problem typ trs
    setR rr = mapR (const rr)

class IsProblem typ => IsDPProblem typ where
    getP     :: Problem typ trs -> trs
    mapP     :: (trs -> trs) -> Problem typ trs -> Problem typ trs
    setP     :: trs -> Problem typ trs -> Problem typ trs
    setP rr = mapP (const rr)

class IsProblem typ => MkProblem typ trs where
    mkProblem    :: (rules ~ trs) => typ -> rules -> Problem typ trs

class IsDPProblem typ => MkDPProblem typ trs where
    mkDPProblem    :: (rules ~ trs, pairs ~ trs) => typ -> rules -> pairs -> Problem typ trs
