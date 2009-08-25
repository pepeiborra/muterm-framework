{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
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
, Dispatch(..)

, ProblemInfo(..), SomeProblem(..), someProblem
, ProofInfo (..), SomeInfo (..), someInfo

-- * Exported functions
, mkDispatcher

, success, singleP, andP, stage, dontKnow, failP, mand, mprod
, runProof, runProofSol, runProofSol', runProofByStages, isSuccess

) where


import Control.Monad as M (MonadPlus(..), msum, liftM, join, (>>=))
import Control.Monad.Free (MonadFree(..), Free (..), foldFree)
import Control.Applicative((<$>))
import Data.Maybe (fromMaybe, isNothing, isJust, catMaybes, listToMaybe)
import System.IO.Unsafe (unsafePerformIO)
import Text.XHtml (HTML(..))

import Control.Applicative
import Data.DeriveTH
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..))
import Data.Traversable as T (Traversable(..), foldMapDefault)

import MuTerm.Framework.Problem
import MuTerm.Framework.Ppr (Ppr(..), text, (<+>), Doc)

import Prelude as P

-----------------------------------------------------------------------------
-- Proof Tree
-----------------------------------------------------------------------------

-- | Proof Tree constructors
data ProofF k =
    And     {procInfo :: !(SomeInfo), problem :: !(SomeProblem), subProblems::[k]}
  | Or      {procInfo :: !(SomeInfo), problem :: !(SomeProblem), subProblems::[k]}
  | Single  {procInfo :: !(SomeInfo), problem :: !(SomeProblem), subProblem::k}
  | Success {procInfo :: !(SomeInfo), problem :: !(SomeProblem)}
  | Fail    {procInfo :: !(SomeInfo), problem :: !(SomeProblem)}
  | DontKnow{procInfo :: !(SomeInfo), problem :: !(SomeProblem)}
  | Stage k
  | MPlus k k
  | MZero
  | MAnd  k k
  | MDone

-- | 'Proof' is a Free Monad. We use this monad to obtain some
-- advantages of monads for free
type Proof a = Free (ProofF) a

-- | 'SomeInfo' hides the type of the proccesor info
data SomeInfo where
    SomeInfo :: ProofInfo p => p -> SomeInfo

-- | 'SomeProblem' hides the type of the problem
data SomeProblem where
    SomeProblem :: (HTML (DPProblem typ a), Ppr (DPProblem typ a), DotRep (DPProblem typ a)) => DPProblem typ a -> SomeProblem

instance Show SomeProblem where
  show _ = "SomeProblem"


-- ------------------
-- Solution datatype
-- ------------------
-- | Solution is the result of the evaluation
data Solution a = YES a
                | NO  a
                | MAYBE

isNo NO{} = True; isNo _ = False
isMaybe MAYBE{} = True; isMaybe _ = False
isYes YES{} = True; isYes _ = False

catYes []               = []
catYes ((YES sol):sols) = sol:(catYes sols)
catYes (_:sols)         = catYes sols

mapYes f (YES x) = YES x
mapYes _ x       = x

-- | Isomorphic to the Maybe monad (return == YES)
instance Monad Solution where
  return = YES
  YES a >>= f = f a
  NO  a >>= f = f a
  MAYBE >>= _ = MAYBE

-- | The MonadPlus instance elegantly enforces the priority of NO over YES
instance MonadPlus Solution where
  mzero = MAYBE
  YES a `mplus` NO b = NO b
  YES a `mplus` _    = YES a
  NO  a `mplus` _    = NO  a
  MAYBE `mplus` b    = b

-----------------------------------------------------------------------------
-- Classes
-----------------------------------------------------------------------------

mkDispatcher :: (a -> Proof b) ->  a -> Proof ()
mkDispatcher f = fmap (const ()) . f

class IsDPProblem typ => Dispatch typ trs where
    dispatch :: DPProblem typ trs -> Proof ()

-- | Class that show the info of the proofs in the desired format
class (HTML p, Ppr p) => ProofInfo p where

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

instance ProofInfo SomeInfo

instance HTML SomeInfo where toHtml (SomeInfo i) = toHtml i

-----------------------------------------------------------------------------
-- Smart Constructors
-----------------------------------------------------------------------------

-- | Return a success node
success :: (ProofInfo p, HTML (DPProblem typ a), Ppr (DPProblem typ a)) => p -> DPProblem typ a -> Proof b
success pi p0 = Impure (Success (someInfo pi) (someProblem p0))

-- | Return a fail node
failP :: (ProofInfo p, HTML (DPProblem typ a), Ppr (DPProblem typ a)) => p -> DPProblem typ a -> Proof b
failP pi p0 = Impure (Fail (someInfo pi) (someProblem p0))

-- | Returns a don't know node
dontKnow :: (ProofInfo p, HTML (DPProblem typ a), Ppr (DPProblem typ a)) => p -> DPProblem typ a -> Proof b
dontKnow pi p0 = Impure (DontKnow (someInfo pi) (someProblem p0))

-- | Return a new single node
singleP :: (ProofInfo p, HTML (DPProblem typ a), Ppr (DPProblem typ a)) => p -> DPProblem typ a -> b -> Proof b
singleP pi p0 p = Impure (Single (someInfo pi) (someProblem p0) (return p))

-- | Return a list of nodes
andP :: (ProofInfo p, HTML (DPProblem typ a), Ppr (DPProblem typ a)) => p -> DPProblem typ a -> [b] -> Proof b
andP pi p0 [] = success pi p0
andP pi p0 pp = Impure (And (someInfo pi) (someProblem p0) (map return pp))

-- | Return a decision among nodes
orP :: (ProofInfo pi, HTML (DPProblem typ a), Ppr (DPProblem typ a)) => pi -> DPProblem typ a -> [b] -> Proof b
orP pi p0 [] = success pi p0
opP pi p0 pp = Impure (Or (someInfo pi) p0 (map return pp))

-- | Returns an extern computation node
stage :: IO (Proof a) -> Proof a
stage = unsafePerformIO

mand :: a -> a -> Proof a
mand a b = Impure (MAnd (return a) (return b))

mprod = P.foldr mand (Impure MDone) . map return where
  mand a (Impure MDone) = a
  mand a b = Impure (MAnd a b)

-- ---------
-- Functions
-- ---------

-- | Pack the proof information
someInfo :: ProofInfo p => p -> SomeInfo
someInfo = SomeInfo

-- | Pack the problem
someProblem :: (ProblemInfo (DPProblem typ a)) => DPProblem typ a -> SomeProblem
someProblem = SomeProblem

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
evalF DontKnow{}    = Nothing
evalF (MPlus p1 p2) = case p1 of
                        Just _  -> p1
                        Nothing -> p2
evalF MZero         = Nothing


-- | We obtain the solution if it exist
evalSolF :: ProofF (Solution [SomeInfo]) -> Solution [SomeInfo]
evalSolF Single { procInfo   = procInfo'
                , subProblem = subProblem'}
    = mapYes (procInfo':) subProblem'

evalSolF And { procInfo    = procInfo'
             , subProblems = subProblems'}
    = if (or . map isMaybe $ subProblems') then
          MAYBE
      else
          if (not . null $ noSubProblems) then
              head noSubProblems
          else
              YES $ procInfo':(concat . catYes $ subProblems')
    where noSubProblems = filter isNo subProblems'

evalSolF Or { procInfo    = procInfo'
            , subProblems = subProblems'}
    = if (or . map (not . isMaybe) $ subProblems') then
          case getSol subProblems' of
            YES sol -> YES $ procInfo':sol
            NO  sol -> NO sol
      else
          MAYBE
    where -- we ensure that getSol [] never occurs
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


-- | Obtain the solution, collecting the proof path in the way
evalSolF' :: (MonadFree ProofF proof, MonadPlus mp) => ProofF (mp (proof a)) -> mp (proof a)
evalSolF' Fail{..}       = mzero -- return (wrap Fail{..})
evalSolF' DontKnow{}     = mzero
evalSolF' MZero          = mzero
evalSolF' MDone          = return (wrap MDone)
evalSolF' Success{..}    = return (wrap Success{..})
evalSolF' (MPlus p1 p2)  = p1 `M.mplus` p2
evalSolF' (And pi pb []) = return (wrap $ Success pi pb)
evalSolF' (And pi pb ll) = (wrap . And  pi pb) `liftM` P.sequence ll
evalSolF' (Or  pi pb []) = return (wrap $ Success pi pb)
evalSolF' (Or  pi pb ll) = (wrap . Single pi pb) `liftM` msum ll
evalSolF' (MAnd  p1 p2)  = p1 >>= \s1 -> p2 >>= \s2 ->
                           return (wrap $ MAnd s1 s2)
evalSolF' (Single pi pb p) = (wrap . Single pi pb) `liftM` p
evalSolF' (Stage  p) = p

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

-- | Apply the evaluation returning the relevant proof subtree
runProofSol' :: Proof a -> Solution (Proof ())
runProofSol' = foldFree (\_ -> MAYBE) evalSolF'

-- | Run the search until a staged node is reached,
--   then run the staged nodes. This is intended to
--   simulates breadth-first search when the staged
--   nodes are expensive.
runProofByStages :: (MonadFree ProofF proof) => Proof a -> Solution (proof b)
runProofByStages p = search where
  -- First turn the proof, i.e. a tree of problems, into a tree of proofs.
  -- This is done by replacing stage nodes by leafs containing the staged subproof
  p'     = stageProof p
  search = do
  -- Next we define the search, which is done using eval.
  -- The search returns a mp list of (potentially) succesful proofs, i.e. tree of problems.
    sol <- foldFree return evalSolF' p'
    -- we search through these one by one
    -- WE SHOULD SORT THEM FIRST
    -- by whether they are a staged proof or not,
    -- so that we look at the easy wins first.
    -- Ultimately runProofDirect performs a good old search over every proof,
    -- regarding any remaining unsolved problem as a failure
    runProofDirect (sol `asTypeOf` p)

  runProofDirect p = foldFree (const mzero) evalSolF' p `asTypeOf` search
--  stageProof :: MonadFree ProofF m => ProofC a -> m (m a)
  stageProof = foldFree (return . return) f where
    f (Stage p) = return (unstageProof p)
    f x = wrap x
    unstageProof = join
