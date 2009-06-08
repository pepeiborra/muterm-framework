{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Framework.Problem
-- Copyright   :  (c) muterm development team
-- License     :  see LICENSE
-- 
-- Maintainer  :  jiborra@dsic.upv.es
-- Stability   :  unstable
-- Portability :  non-portable 
--
-- This module contains the different muterm problems with its type.
--
-----------------------------------------------------------------------------

module Framework.Problem (

-- * Exported data

ProblemF (..), Problem, RProblem, DPProblem

-- * Exported functions

, mkProblem, getR, getP

) where


-- Different kind of problems we can instantiate in the ProblemF GADT

data RProblem    -- ^ Rewriting problem
data IRProblem   -- ^ Innermost rewriting problem
data CSRProblem  -- ^ Context-sensitive rewriting problem
data ICSRProblem -- ^ Innermost context-sensitive rewriting 
                               -- problem
data OSRProblem  -- ^ Order-sorted rewriting problem
data DPProblem   -- ^ Dependency pairs problem

-- | GADT where 'ptype' is instantiated to the desired problem
data ProblemF ptype a where
  Rewriting    :: a -> ProblemF RProblem a
  IRewriting   :: a -> ProblemF IRProblem a
  CSRewriting  :: a -> ProblemF CSRProblem a
  ICSRewriting :: a -> ProblemF ICSRProblem a
  OSRewriting  :: a -> ProblemF OSRProblem a
  DPFProblem   :: a -> a -> ProblemF DPProblem a

-- | Alias to call a 'Problem'
type Problem ptype trs   = ProblemF ptype trs

-- 'ProblemF' is a functor
instance Functor (ProblemF a) where
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

-- | Function to create a problem
mkProblem :: (a -> ProblemF b a) -> a -> ProblemF b a
mkProblem ptype trs = ptype trs

-- | Get TRS rules
getR :: ProblemF DPProblem a -> a
getR (DPFProblem p r) = r  

-- | Get DPTRS rules
getP :: ProblemF DPProblem a -> a
getP (DPFProblem p r) = p