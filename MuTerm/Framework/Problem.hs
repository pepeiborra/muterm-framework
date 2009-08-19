{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
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

  Problem (..)
, RProblem, IRProblem, CSRProblem, ICSRProblem, OSRProblem
, DPProblem, CSDPProblem
, SomeProblem (..)
--,  RewProblem, CSRewProblem, TermProblem, CSTermProblem

-- * Exported functions

, mkProblem, mkDPProblem, mkCSDPProblem, getR, getP, getCSP, getCSR, getCSS, someProblem

) where

import MuTerm.Framework.Ppr (Ppr (..))

import Control.Monad (liftM)
import Control.Monad.Reader (MonadReader (..))

-----------------------------------------------------------------------------
-- Data
-----------------------------------------------------------------------------

-- Different kind of problems we can instantiate in the ProblemF GADT

data RProblem    -- ^ Rewriting problem
data IRProblem   -- ^ Innermost rewriting problem
data CSRProblem  -- ^ Context-sensitive rewriting problem
data ICSRProblem -- ^ Innermost context-sensitive rewriting 
                               -- problem
data OSRProblem  -- ^ Order-sorted rewriting problem
data DPProblem   -- ^ Dependency pairs problem
data CSDPProblem -- ^ Context-sensitive dependency pairs problem

-- | GADT where 'ptype' is instantiated to the desired problem
data Problem ptype a where
  Rewriting    :: a -> Problem RProblem a
  IRewriting   :: a -> Problem IRProblem a
  CSRewriting  :: a -> Problem CSRProblem a
  ICSRewriting :: a -> Problem ICSRProblem a
  OSRewriting  :: a -> Problem OSRProblem a
  DPFProblem   :: a -> a -> Problem DPProblem a
  CSDPFProblem :: a -> a -> a -> Problem CSDPProblem a

-- | 'SomeProblem' hides the type of the problem
data SomeProblem where
    SomeProblem :: Ppr a => !(Problem ptype a) -> SomeProblem

-----------------------------------------------------------------------------
-- Instances
-----------------------------------------------------------------------------

-- Functor

instance Functor (Problem a) where
  fmap f (Rewriting trs)    
      = Rewriting (f trs)
  fmap f (IRewriting trs)   
      = IRewriting (f trs)
  fmap f (CSRewriting trs)  
      = CSRewriting (f trs)
  fmap f (ICSRewriting trs) 
      = ICSRewriting (f trs)
  fmap f (OSRewriting trs)  
      = OSRewriting (f trs)
  fmap f (DPFProblem trs dps) 
      = DPFProblem (f trs) (f dps)

-- Show

instance Show (Problem ptype a) where
  show _ = "Problem"

instance Show SomeProblem where
  show _ = "SomeProblem"

-- Ppr 

instance Ppr a => Ppr (Problem ptype a) where
  pprBase (Rewriting r)     = pprBase r
  pprBase (CSRewriting r)   = pprBase r
  pprBase (CSDPFProblem p r s) = pprBase p

instance Ppr SomeProblem where
  pprBase (SomeProblem p) = pprBase p

-----------------------------------------------------------------------------
-- Functions
-----------------------------------------------------------------------------

-- | Function to create a problem
mkProblem :: (a -> Problem b a) -> a -> Problem b a
mkProblem ptype trs = ptype trs

-- | Function to create a DP problem
mkDPProblem :: (a -> a -> Problem b a) -> a -> a -> Problem b a
mkDPProblem ptype p r = ptype p r

-- | Function to create a DP problem
mkCSDPProblem :: (a -> a -> a -> Problem b a) -> a -> a -> a -> Problem b a
mkCSDPProblem ptype p r s = ptype p r s

-- | Get pairs
getP :: Problem DPProblem a -> a
getP (DPFProblem p r) = p

-- | Get rules
getR :: Problem DPProblem a -> a
getR (DPFProblem p r) = r  

-- | Get cs-pairs
getCSP :: Problem CSDPProblem a -> a
getCSP (CSDPFProblem p r s) = p

-- | Get cs-rules
getCSR :: Problem CSDPProblem a -> a
getCSR (CSDPFProblem p r s) = r  

-- | Get unhiding trs
getCSS :: Problem CSDPProblem a -> a
getCSS (CSDPFProblem p r s) = s

-- | Pack the problem
someProblem :: Ppr a => Problem problem a -> SomeProblem
someProblem = SomeProblem
