{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
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

IsProblem(..), IsDPProblem(..),
MkProblem(..), MkDPProblem(..),
setR, setP, mapR, mapP, mkDPProblem,
mkDerivedProblem, mkDerivedDPProblem, mapFramework,
mkDerivedDPProblemO, mapFrameworkO
) where

import Data.Typeable
import Debug.Hoed.Observe

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

class (Functor (Problem typ)) => IsProblem typ where
    data Problem typ :: * -> *
    getFramework :: Problem typ trs -> typ
    getR         :: Problem typ trs -> trs

deriving instance Typeable Problem

class IsProblem typ => IsDPProblem typ where
    getP     :: Problem typ trs -> trs

class IsProblem typ => MkProblem typ trs where
    mkProblem  :: (rules ~ trs) => typ -> rules -> Problem typ trs
    mapRO      :: Observer -> (trs -> trs) -> Problem typ trs -> Problem typ trs
    setRO      :: Observer -> trs -> Problem typ trs -> Problem typ trs
    setRO o rr  = mapRO o (const rr)
    mapRO o f p = setRO o (f $ getR p) p

setR x = setRO nilObserver x
mapR f = mapRO nilObserver f

class (IsDPProblem typ, MkProblem typ trs) => MkDPProblem typ trs where
    mkDPProblemO :: (rules ~ trs, pairs ~ trs) => Observer -> typ -> rules -> pairs -> Problem typ trs
    mapPO        :: Observer -> (trs -> trs) -> Problem typ trs -> Problem typ trs
    setPO        :: Observer ->trs -> Problem typ trs -> Problem typ trs
    setPO o rr    = mapPO o (const rr)
    mapPO o f p   = setPO o (f (getP p)) p

mkDPProblem typ = mkDPProblemO nilObserver typ
setP x = setPO nilObserver x
mapP f = mapPO nilObserver f

mkDerivedProblem :: (IsProblem typ, MkProblem typ' trs) => typ' -> Problem typ trs -> Problem typ' trs
mkDerivedProblem typ p = mkProblem typ (getR p)

mkDerivedDPProblem :: (IsDPProblem typ, MkDPProblem typ' trs) => typ' -> Problem typ trs -> Problem typ' trs
mkDerivedDPProblem typ p = mkDPProblem typ (getR p) (getP p)

mkDerivedDPProblemO :: (IsDPProblem typ, MkDPProblem typ' trs
                       ) => Observer -> typ' -> Problem typ trs -> Problem typ' trs
mkDerivedDPProblemO o typ p = mkDPProblemO o typ (getR p) (getP p)

mapFramework :: (IsDPProblem typ, MkDPProblem typ' trs) => (typ -> typ') -> Problem typ trs -> Problem typ' trs
mapFramework f p = mkDerivedDPProblem (f $ getFramework p) p

mapFrameworkO :: (IsDPProblem typ, MkDPProblem typ' trs) => Observer -> (typ -> typ') -> Problem typ trs -> Problem typ' trs
mapFrameworkO o f p = mkDerivedDPProblemO o (f $ getFramework p) p
