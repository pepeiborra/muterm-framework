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
Processor(..), apply, applySearch, applyE,
Res
) where
import Control.Exception
import Control.Monad.Free
import Data.Suitable
import Data.Traversable (Traversable)
import MuTerm.Framework.Proof (Proof,Info,search,aborted)
import MuTerm.Framework.Problem
import System.IO.Unsafe
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
  applyO      :: ( Info (InfoConstraint tag) inp
                 , Info (InfoConstraint tag) (Res tag inp)
                 ) =>
                 Observer -> tag -> inp ->  Proof (InfoConstraint tag) (Problem (Typ tag inp) (Trs tag inp))

  applySearchO :: ( Info (InfoConstraint tag) inp
                  , Info (InfoConstraint tag) (Res tag inp)
                  ) =>
                  Observer -> tag -> inp -> [Proof (InfoConstraint tag) (Problem (Typ tag inp) (Trs tag inp))]


  applyO       o tag p = search( applySearchO o tag p)
  applySearchO o tag p = [applyO o tag p]

apply       p = applyO       nilObserver p
applySearch p = applySearchO nilObserver p

applyE tag inp = unsafePerformIO $ do
  evaluate(apply tag inp) `catch` \e -> return $ aborted (show (e :: SomeException))
