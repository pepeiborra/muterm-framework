{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
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
-- This module contains the proof functor.
--
-----------------------------------------------------------------------------

module MuTerm.Framework.Proof (

-- * Exported data

ProofF(..), Proof, Solution (..)

-- * Exported classes

, ProofInfo (..), SomeInfo (..)

-- * Exported function

, success, singleP, andP, runProof, runProofSol, stage, dontKnow
, choiceP, failP

) where


import Control.Monad (MonadPlus (..), msum, liftM, join, (>>=))
import Control.Monad.Free (Free (..), foldFree)
import Control.Applicative((<$>))
import MuTerm.Framework.Problem (Problem (..), SomeProblem (..), someProblem)
import Data.Maybe (fromMaybe, isNothing, isJust, catMaybes)
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad.Reader (MonadReader (..))
import Control.Applicative
import Data.DeriveTH
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..))
import Data.Traversable as T (Traversable(..), foldMapDefault)
import MuTerm.Framework.Ppr (Ppr(..), text, (<+>), Doc)
--import Control.Monad.Cont (MonadCont (..), runCont)

-----------------------------------------------------------------------------
-- Data
-----------------------------------------------------------------------------

-- | Solution is the result of the evaluation
data Solution a = YES a
                | NO  a
                | MAYBE

-- | 'SomeInfo' hides the type of the proccesor info
data SomeInfo where
    SomeInfo :: ProofInfo p => p -> SomeInfo

-- | Possible returning proofs after appliying a processor
data ProofF k = Single { procInfo :: !(SomeInfo)       -- ^ processor info
                       , subProblem :: k}              -- ^ subproblem
              | And { procInfo :: !(SomeInfo)          -- ^ processor info
                    , subProblems::[k]}                -- ^ list of subproblems
              | Or {procInfo :: !(SomeInfo)            -- ^ processor info
                   , subProblems::[k]}                 -- ^ list of subproblems
              | Success {procInfo :: !(SomeInfo)}      -- ^ processor info
              | Fail {procInfo :: !(SomeInfo)}         -- ^ processor info
              | DontKnow
              | Stage k                                -- ^ using external
                                                       -- computations
              | MPlus k k
              | MZero
                deriving (Show)

-- | 'Proof' is a Free Monad. We use this monad to obtain some
-- advantages of monads for free
type Proof a = Free (ProofF) a

-----------------------------------------------------------------------------
-- Classes
-----------------------------------------------------------------------------

-- | Class that show the info of the proofs in the desired format
class Ppr p => ProofInfo p where
    showPlain :: p -> String
    pprPlain  :: p -> Doc
--    showInfo  :: Output -> p -> String
--    showInfo f = case f of
--                   Plain -> showPlain

-----------------------------------------------------------------------------
-- Instances
-----------------------------------------------------------------------------

instance Foldable ProofF where foldMap = T.foldMapDefault
$(derive makeFunctor     ''Solution)
$(derive makeFunctor     ''ProofF)
$(derive makeTraversable ''ProofF)

-- MonadPlus

instance MonadPlus (Free (ProofF)) where 
    mzero       = Impure MZero
    mplus p1 p2 = Impure (MPlus p1 p2) 
                  -- if isSuccess p1 then p1 else choiceP p1 p2

-- Show

instance Show SomeInfo where
    show (SomeInfo p) = show (ppr p)

-- Ppr

instance Ppr SomeInfo where
    ppr (SomeInfo p) = ppr p

-----------------------------------------------------------------------------
-- Functions
-----------------------------------------------------------------------------

-- | Return a success node
success :: (ProofInfo p) => p -> Proof b
success pi = Impure (Success (someInfo pi))

-- | Return a fail node
failP :: (ProofInfo p) => p -> Proof b
failP pi = Impure (Fail (someInfo pi))

-- | Return a new single node
singleP :: (ProofInfo p) => p -> b -> Proof b
singleP pi p = Impure (Single (someInfo pi) (return p))

-- | Return a list of nodes
andP :: (ProofInfo p) => p -> [b] -> Proof b
andP pi [] = success pi
andP pi pp = Impure (And (someInfo pi) (map return pp))

-- | Return a decision among nodes
orP :: (ProofInfo p) => p -> [b] -> Proof b
orP pi [] = success pi
opP pi pp = Impure (Or (someInfo pi) (map return pp))

-- | The or version with mplus
choiceP :: Proof a -> Proof a -> Proof a
choiceP p1 p2 = Impure (MPlus p1 p2)

-- | Returns a don't know node
dontKnow :: Proof b
dontKnow = Impure DontKnow

-- | Returns an extern computation node
stage :: IO (Proof a) -> Proof a
stage = unsafePerformIO

-- | Pack the proof information
someInfo :: ProofInfo p => p -> SomeInfo
someInfo = SomeInfo

-- | We obtain if the proof is a solution
isSuccessF :: ProofF Bool -> Bool
isSuccessF Single { procInfo    = SomeInfo procInfo'
                  , subProblem = subProblem'} 
                         = subProblem'
isSuccessF And { subProblems = subProblems'} 
                         = and subProblems'
isSuccessF Or { subProblems = subProblems'} 
                         = or subProblems'
isSuccessF Success {}    = True
isSuccessF Fail {}       = False
isSuccessF DontKnow {}   = False
isSuccessF (MPlus p1 p2) = p1 || p2
isSuccessF MZero         = False

-- | We obtain the solution if it exist
--evalF :: MonadCont m => ProofF (Maybe [SomeInfo]) -> m (Maybe [SomeInfo])
evalF :: ProofF (Maybe [SomeInfo]) -> Maybe [SomeInfo]
evalF Single { procInfo   = procInfo'
             , subProblem = subProblem'} 
    = case subProblem' of
        Nothing  -> Nothing
        Just sol -> Just $ procInfo':sol
evalF And { procInfo    = procInfo'
          , subProblems = subProblems'} 
    = if (or . map isNothing $ subProblems') then
          Nothing
      else
          (Just $ procInfo':(concat . catMaybes $ subProblems'))
evalF Or { procInfo    = procInfo'
         , subProblems = subProblems'} 
    = if (or . map isJust $ subProblems') then
          (Just $ procInfo':(head . catMaybes $ subProblems'))
      else
          Nothing
evalF Success { procInfo = procInfo' } = Just [procInfo']
evalF Fail {}       = Nothing
evalF DontKnow      = Nothing
evalF (MPlus p1 p2) = case p1 of
                        Just _  -> p1
                        Nothing -> p2
evalF MZero         = Nothing

-- | We obtain the solution if it exist
evalSolF :: ProofF (Solution [SomeInfo]) -> Solution [SomeInfo]
evalSolF Single { procInfo   = procInfo'
                , subProblem = subProblem'} 
    = case subProblem' of
        MAYBE   -> MAYBE
        YES sol -> YES $ procInfo':sol
        NO  sol -> NO sol
evalSolF And { procInfo    = procInfo'
             , subProblems = subProblems'} 
    = if (or . map isMaybe $ subProblems') then
          MAYBE
      else
          if (not . null $ noSubProblems) then
              head noSubProblems
          else
              YES $ procInfo':(concat . catYes $ subProblems')
    where isMaybe MAYBE   = True
          isMaybe (YES _) = False
          isMaybe (NO  _) = False
          noSubProblems = filter isNo subProblems'
          isNo MAYBE   = False
          isNo (YES _) = False
          isNo (NO  _) = True
          catYes []               = []
          catYes ((YES sol):sols) = sol:(catYes sols)
          catYes (_:sols)         = catYes sols
evalSolF Or { procInfo    = procInfo'
            , subProblems = subProblems'} 
    = if (or . map (not . isMaybe) $ subProblems') then
          case getSol subProblems' of
            YES sol -> YES $ procInfo':sol
            NO  sol -> NO sol
      else
          MAYBE
    where isMaybe MAYBE   = True
          isMaybe (YES _) = False
          isMaybe (NO  _) = False
          -- we ensure that getSol [] never occurs
          getSol ((YES sol):sols) = YES sol
          getSol ((NO sol):sols)  = NO sol
          getSol (_:sols)         = getSol sols
evalSolF Success { procInfo = procInfo' } = YES [procInfo']
evalSolF Fail { procInfo = procInfo' }    = NO [procInfo']
evalSolF DontKnow {}   = MAYBE
evalSolF (MPlus p1 p2) = case p1 of
                           YES _     -> p1
                           NO  _     -> p1
                           MAYBE     -> p2
evalSolF MZero         = MAYBE

-- Apply search algorithms

-- | Evaluate if proof is success
isSuccess :: Proof a -> Bool
isSuccess = foldFree (const False) isSuccessF

-- | Evaluate the proof
evaluate :: Proof a -> Maybe [SomeInfo]
evaluate = foldFree (\_ -> Nothing) evalF

-- | Evaluate the proof controlling non-termination
evaluateSol :: Proof a -> Solution [SomeInfo]
evaluateSol = foldFree (\_ -> MAYBE) evalSolF

-- | Apply the evaluation
runProof :: (Show a) => Proof a -> Maybe [SomeInfo]
runProof p = evaluate p

-- | Apply the evaluation
runProofSol :: (Show a) => Proof a -> Solution [SomeInfo]
runProofSol p = evaluateSol p
