{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE KindSignatures #-}
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

, ProblemInfo, SomeProblem(..), someProblem
, ProofInfo, SomeInfo (..), someInfo

-- * Exported functions
, mkDispatcher

, success, singleP, andP, dontKnow, failP, mand, mprod
, isSuccess, runProof -- , runProof, runProofSol', runProofByStages

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
import MuTerm.Framework.DotRep

import Prelude as P

-----------------------------------------------------------------------------
-- Proof Tree
-----------------------------------------------------------------------------

-- | Proof Tree constructors
data ProofF (m :: * -> *) (k :: *) =
    And     {procInfo :: !(SomeInfo), problem :: !(SomeProblem), subProblems::[k]}
  | Or      {procInfo :: !(SomeInfo), problem :: !(SomeProblem), alternatives::m k}
  | Single  {procInfo :: !(SomeInfo), problem :: !(SomeProblem), subProblem::k}
  | Success {procInfo :: !(SomeInfo), problem :: !(SomeProblem)}
  | Fail    {procInfo :: !(SomeInfo), problem :: !(SomeProblem)}
  | DontKnow{procInfo :: !(SomeInfo), problem :: !(SomeProblem)}
  | Search (m k)
  | MAnd  k k
  | MDone

-- -------------------
-- Sebastian's monad
-- -------------------
data ProofS m a =
    PureS a
  | AndS  [ProofS m a]
  | LazyS (m (ProofS m a))

type ProofListT a = [ProofS [] a]

instance Monad m => Monad (ProofS m) where
  return = PureS
  PureS a >>= f = f a
  AndS aa >>= f = AndS (P.map (>>=f) aa)
  LazyS a >>= f = LazyS (liftM (>>= f) a)

runProofS :: MonadPlus m => ProofS m a -> m (ProofS t a)
runProofS = foldProofS (return . PureS) (liftM AndS . P.sequence) join

foldProofS :: (a -> b) -> ([b] -> b) -> (m b -> b) -> ProofS m a -> b
foldProofS = undefined


-- | 'Proof' is a Free Monad. 'm' is the MonadPlus used for search
type Proof m a = Free (ProofF m) a

-- | 'SomeInfo' hides the type of the proccesor info
data SomeInfo where
    SomeInfo :: ProofInfo p => p -> SomeInfo

-- | 'SomeProblem' hides the type of the problem
data SomeProblem where
    SomeProblem :: (HTML p, Ppr p, DotRep p) => p -> SomeProblem

instance Show SomeProblem where
  show _ = "SomeProblem"
{-
f :: Proof a -> IO (Proof a)
f = lift . foldFree g where
  g (Stage k) = k >>= id
  g (t :: ProofF (IO (Proof a))) = fmap Impure (sequence t)
-}



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

mkDispatcher :: Monad m => (a -> Proof m b) ->  a -> Proof m ()
mkDispatcher f = fmap (const ()) . f

class IsDPProblem typ => Dispatch typ trs where
    dispatch :: MonadPlus m => DPProblem typ trs -> Proof m ()

-- | Class that show the info of the proofs in the desired format
class (HTML p, Ppr p, DotRep p) => ProofInfo p
class (HTML p, Ppr p, DotRep p) => ProblemInfo p

instance (HTML (DPProblem typ trs), Ppr (DPProblem typ trs), DotRep (DPProblem typ trs)) => ProblemInfo (DPProblem typ trs)

instance Ppr SomeInfo where ppr (SomeInfo p) = ppr p
instance Ppr  SomeProblem where ppr (SomeProblem p) = ppr p

instance HTML SomeInfo where toHtml (SomeInfo i) = toHtml i
instance HTML SomeProblem where toHtml  (SomeProblem p) = toHtml p

instance DotRep SomeProblem where dot (SomeProblem p) = dot p; dotSimple (SomeProblem p) = dotSimple p
instance DotRep SomeInfo where dot (SomeInfo p) = dot p; dotSimple (SomeInfo p) = dotSimple p

instance ProofInfo SomeInfo
instance ProofInfo SomeProblem

-----------------------------------------------------------------------------
-- Instances
-----------------------------------------------------------------------------
$(derive (makeFunctorN 1)     ''Solution)

instance Monad m => Functor (ProofF m) where
  fmap f (And pi p kk)   = And pi p (fmap f kk)
  fmap f (Single pi p k) = Single pi p (f k)
  fmap _ (Success pi p)  = Success pi p
  fmap _ (Fail pi p)     = Fail pi p
  fmap _ (DontKnow pi p) = DontKnow pi p
  fmap f (Search mk)     = Search (liftM f mk)
  fmap f (MAnd k1 k2)    = MAnd (f k1) (f k2)
  fmap f MDone           = MDone

instance (Monad m, Traversable m) => Foldable (ProofF m) where foldMap = T.foldMapDefault

instance (Monad m, Traversable m) => Traversable (ProofF m) where
  traverse f (And pi p kk)   = And pi p <$> traverse f kk
  traverse f (Single pi p k) = Single pi p <$> f k
  traverse _ (Success pi p)  = pure $ Success pi p
  traverse _ (Fail pi p)     = pure $ Fail pi p
  traverse _ (DontKnow pi p) = pure $ DontKnow pi p
  traverse f (Search mk)     = Search <$> traverse f mk
  traverse f (MAnd k1 k2)    = MAnd <$> f k1 <*> f k2
  traverse f MDone           = pure MDone


-- MonadPlus

instance MonadPlus m => MonadPlus (Free (ProofF m)) where
    mzero       = Impure (Search mzero)
    mplus p1 p2 = Impure (Search (mplus (return p1) (return p2)))

-- Show

instance Show SomeInfo where
    show (SomeInfo p) = show (ppr p)

-- Default 'bogus' Instances of Representation classes

instance Ppr a => DotRep a where dot    x = Text (ppr x) []
instance Ppr a => HTML   a where toHtml x = toHtml (show $ ppr x)

-----------------------------------------------------------------------------
-- Smart Constructors
-----------------------------------------------------------------------------

-- | Return a success node
success :: (ProofInfo p, ProblemInfo problem, Monad m) => p -> problem -> Proof m b
success pi p0 = Impure (Success (someInfo pi) (someProblem p0))

-- | Return a fail node
failP :: (ProofInfo p, ProblemInfo problem, Monad m) => p -> problem -> Proof m b
failP pi p0 = Impure (Fail (someInfo pi) (someProblem p0))

-- | Returns a don't know node
dontKnow :: (ProofInfo p, ProblemInfo problem, Monad m) => p -> problem -> Proof m b
dontKnow pi p0 = Impure (DontKnow (someInfo pi) (someProblem p0))

-- | Return a new single node
singleP :: (ProofInfo p, ProblemInfo problem, Monad m) => p -> problem -> b -> Proof m b
singleP pi p0 p = Impure (Single (someInfo pi) (someProblem p0) (return p))

-- | Return a list of nodes
andP :: (ProofInfo p, ProblemInfo problem, Monad m) => p -> problem -> [b] -> Proof m b
andP pi p0 [] = success pi p0
andP pi p0 pp = Impure (And (someInfo pi) (someProblem p0) (map return pp))

mand :: Monad m => a -> a -> Proof m a
mand a b = Impure (MAnd (return a) (return b))

mprod :: Monad m => [a] -> Proof m a
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
someProblem :: ProblemInfo p => p -> SomeProblem
someProblem = SomeProblem

{-
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
-}

-- | Obtain the solution, collecting the proof path in the way
evalSolF' :: (MonadPlus mp) => ProofF mp (mp(Proof t a)) -> mp (Proof t a)
evalSolF' Fail{..}       = mzero -- return (wrap Fail{..})
evalSolF' DontKnow{}     = mzero
evalSolF' MDone          = return (Impure MDone)
evalSolF' Success{..}    = return (Impure Success{..})
evalSolF' (Search mk)    = join mk
evalSolF' (And pi pb []) = return (Impure $ Success pi pb)
evalSolF' (And pi pb ll) = (Impure . And pi pb) `liftM` P.sequence ll
evalSolF' (Or  pi pb ll) = (Impure . Single pi pb) `liftM` join ll
evalSolF' (MAnd  p1 p2)  = p1 >>= \s1 -> p2 >>= \s2 ->
                           return (Impure $ MAnd s1 s2)
evalSolF' (Single pi pb p) = (Impure . Single pi pb) `liftM` p


-- | Evaluate if proof is success
isSuccess :: Proof Maybe a -> Bool
isSuccess = isJust . foldFree (const Nothing) evalSolF'
{-
-- | Evaluate the proof
evaluate :: Proof m a -> Maybe [SomeInfo]
evaluate = foldFree (\_ -> Nothing) evalF

-- | Evaluate the proof controlling non-termination
evaluateSol :: Proof m a -> Solution [SomeInfo]
evaluateSol = foldFree (\_ -> MAYBE) evalSolF

-- | Apply the evaluation
runProof :: (Show a) => Proof m a -> Maybe [SomeInfo]
runProof p = evaluate p

-- | Apply the evaluation
runProofSol :: (Show a) => Proof m a -> Solution [SomeInfo]
runProofSol p = evaluateSol p
-}
-- | Apply the evaluation returning the relevant proof subtree
runProof :: MonadPlus mp => Proof mp a -> mp (Proof m ())
runProof = foldFree (const mzero) evalSolF'
