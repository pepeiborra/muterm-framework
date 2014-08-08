{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, FlexibleInstances, FlexibleContexts #-}
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
InfoConstraint,
Processor(..), apply, applySearch,
Res
) where

import Control.Monad
import Data.Suitable
import Data.Traversable (Traversable)
import MuTerm.Framework.Proof (Proof,Info)
import MuTerm.Framework.Problem

import Debug.Hoed.Observe

-----------------------------------------------------------------------------
-- Classes
-----------------------------------------------------------------------------

type family InfoConstraint tag :: * -> *

type Res tag inp = Problem (Typ tag inp) (Trs tag inp)

-- | Each processor is an instance of the class 'Processor'.
--   The type of the output problem is determined by the type of the input problem
class Processor tag inp where
  type Typ tag inp
  type Trs tag inp
  applyO      :: ( MonadPlus mp
                 , Traversable mp
                 , Observable1 mp
                 , Info (InfoConstraint tag) inp
                 , Info (InfoConstraint tag) (Res tag inp)
                 ) =>
                 Observer -> tag -> inp ->  Proof (InfoConstraint tag) mp (Problem (Typ tag inp) (Trs tag inp))

  applySearchO :: ( MonadPlus mp
                  , Traversable mp
                  , Observable1 mp
                  , Info (InfoConstraint tag) inp
                  , Info (InfoConstraint tag) (Res tag inp)
                  ) =>
                  Observer -> tag -> inp -> [Proof (InfoConstraint tag) mp (Problem (Typ tag inp) (Trs tag inp))]


  applyO       o tag p = case applySearchO o tag p of [p'] -> p' ; pp -> msum pp
  applySearchO o tag p = [applyO o tag p]

apply       p = applyO       nilObserver p
applySearch p = applySearchO nilObserver p
