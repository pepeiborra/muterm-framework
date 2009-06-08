{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE RecordWildCards #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Framework.Proof
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

module Framework.Proof (

-- * Exported data

ProofF(..), Proof

-- * Exported classes

, ProofInfo (..), SomeInfo (..)

-- * Exported function

, success, singleP, andP, runProof, stage, dontKnow, someProblem, fixSolver
, choiceP

) where

import Control.Monad (MonadPlus (..), msum, liftM, join, (>>=))
import Control.Monad.Free (Free (..), foldFree)
import Control.Applicative((<$>))
import Framework.Problem (ProblemF (..))
import Data.Maybe (fromMaybe, isNothing, isJust, catMaybes)

-- | 'SomeProblem' hides the type of the problem
data SomeProblem where
    SomeProblem :: !(ProblemF ptype a) -> SomeProblem

-- | 'SomeInfo' hides the type of the proccesor info
data SomeInfo where
    SomeInfo :: ProofInfo p => p -> SomeInfo

-- | Possible returning proofs after appliying a processor
data ProofF k = Single { procInfo :: !(SomeInfo)       -- ^ processor info
                       , problem :: !(SomeProblem)     -- ^ problem
                       , subProblem :: k}              -- ^ subproblem
              | And { procInfo :: !(SomeInfo)          -- ^ processor info
                    , problem :: !(SomeProblem)        -- ^ problem
                    , subProblems::[k]}                -- ^ list of subproblems
              | Or {procInfo :: !(SomeInfo)            -- ^ processor info
                   , problem :: !(SomeProblem)         -- ^ problem
                   , subProblems::[k]}                 -- ^ list of subproblems
              | Success {procInfo :: !(SomeInfo)       -- ^ processor info
                        , problem :: !(SomeProblem)}   -- ^ problem
              | Fail {procInfo :: !(SomeInfo)          -- ^ processor info
                     , problem :: !(SomeProblem)}      -- ^ problem
              | DontKnow {problem :: !(SomeProblem)}
--              | Stage (IORef (IO k))                   -- ^ using external
                                                         -- computations
              | Stage (IO k)                           -- ^ using external
                                                       -- computations
              | MPlus k k
              | MZero

-- | Proof is a functor
instance Functor (ProofF) where
    fmap f (Single { procInfo    = procInfo'
                   , problem     = problem'
                   , subProblem  = subproblem'
                   })
        = Single { procInfo    = procInfo'
                 , problem     = problem'
                 , subProblem  = f subproblem'
                 }
    fmap f (And { procInfo    = procInfo'
                , problem     = problem'
                , subProblems = subproblems'
                })
        = And { procInfo    = procInfo'
              , problem     = problem'
              , subProblems = fmap f subproblems'
              }
    fmap f (Or { procInfo    = procInfo'
               , problem     = problem'
               , subProblems = subproblems'
               })
        = Or { procInfo    = procInfo'
             , problem     = problem'
             , subProblems = fmap f subproblems'
             }
    fmap f (Success { procInfo    = procInfo'
                    , problem     = problem'
                    })
        = Success { procInfo    = procInfo'
                  , problem     = problem'
                  }
    fmap f (Fail { procInfo    = procInfo'
                 , problem     = problem'
                 })
        = Fail { procInfo    = procInfo'
               , problem     = problem'
               }
    fmap f (DontKnow { problem     = problem' })
        = DontKnow { problem     = problem' }
    fmap f (Stage ioProblem)
        = Stage (do { iop <-  ioProblem
                    ; return (f iop)
                    }
                )
    fmap f (MPlus p1 p2) 
        = MPlus (f p1) (f p2)
    fmap f MZero 
        = MZero

-- | 'Proof' is a Free Monad. We use this monad to obtain some
-- advantages for free
type Proof a = Free (ProofF) a

instance MonadPlus (Free (ProofF)) where 
    mzero       = Impure MZero
    mplus p1 p2 = Impure (MPlus p1 p2) 
                  -- if isSuccess p1 then p1 else choiceP p1 p2
                      
-- | class that show the info of the proofs in the desired format
class ProofInfo p where
    showPlain :: p -> String
--    showInfo  :: Output -> p -> String
--    showInfo f = case f of
--                   Plain -> showPlain

success :: (ProofInfo p) => p -> ProblemF problem a -> Proof b
success pi p0 = Impure (Success (someInfo pi) (someProblem p0))

failP :: (ProofInfo p) => p -> ProblemF problem a -> Proof b
failP pi p0   = Impure (Fail (someInfo pi) (someProblem p0))

singleP :: (ProofInfo p) => p -> ProblemF problem a -> b -> Proof b
singleP pi p0 p = Impure (Single (someInfo pi) (someProblem p0) (return p))

andP :: (ProofInfo p) => p -> ProblemF problem a -> [b] -> Proof b
andP pi p0 [] = success pi p0
andP pi p0 pp = Impure (And (someInfo pi) (someProblem p0) (map return pp))

orP :: (ProofInfo p) => p -> ProblemF problem a -> [b] -> Proof b
orP pi p0 [] = success pi p0
opP pi p0 pp = Impure (Or (someInfo pi) (someProblem p0) (map return pp))

choiceP :: Proof a -> Proof a -> Proof a
choiceP p1 p2 = Impure (MPlus p1 p2)

dontKnow :: ProblemF problem a -> Proof b
dontKnow p0 = Impure (DontKnow (someProblem p0))

stage :: IO (Proof a) -> Proof a
stage = Impure . Stage
--      v <- newIORef ()  

-- | Pack the proof information
someInfo :: ProofInfo p => p -> SomeInfo
someInfo = SomeInfo

-- | Pack the problem
someProblem :: ProblemF problem a -> SomeProblem
someProblem = SomeProblem

-- | We obtain if the proof is a solution
isSuccessF :: ProofF (IO Bool) -> IO Bool
isSuccessF Single { procInfo    = SomeInfo procInfo'
                  , subProblem = subProblem'} 
                         = subProblem'
isSuccessF And { subProblems = subProblems'} 
                         = liftM and . sequence $ subProblems'
isSuccessF Or { subProblems = subProblems'} 
                         = liftM or . sequence $ subProblems'
isSuccessF (Stage ioProof) 
                         = join ioProof
isSuccessF Success {}    = return True
isSuccessF Fail {}       = return False
isSuccessF DontKnow {}   = return False
isSuccessF (MPlus p1 p2) = do { p1' <- p1
                              ; p2' <- p2
                              ; return (p1' || p2')
                              }
isSuccessF MZero         = return False

-- | Evaluate the proof
isSuccess :: Proof a -> IO Bool
isSuccess = foldFree (\_ -> return False) isSuccessF
            -- is equivalent to: foldFree (const False) isSuccessF

-- runProof :: MonadPlus m => Proof a -> IO (m (Proof ()))
runProof :: Proof a -> IO (Maybe [SomeInfo])
runProof = evaluate

-- | We apply the strategy recursively
fixSolver :: (a -> Proof a) -> a -> Proof a
fixSolver f x = let x' = f x in x' `mplus` (x' >>= fixSolver f)

-- | Evaluate the proof
evaluate :: Proof a -> IO (Maybe [SomeInfo])
evaluate = foldFree (\_ -> return Nothing) evalF
            -- is equivalent to: foldFree (const False) isSuccessF


-- | We obtain the solution if it exist
evalF :: ProofF (IO (Maybe [SomeInfo])) -> IO (Maybe [SomeInfo])
evalF Single { procInfo   = procInfo'
             , subProblem = subProblem'} 
    = do p <- subProblem'
         case p of
           Nothing  -> subProblem'
           Just sol -> return . Just $ procInfo':sol
evalF And { procInfo    = procInfo'
          , subProblems = subProblems'} 
    = do andsol <- sequence subProblems'
         if (or . map isNothing $ andsol) then
             return Nothing
           else
             return (Just $ procInfo':(concat . catMaybes $ andsol))
evalF Or { procInfo    = procInfo'
         , subProblems = subProblems'} 
    = do orsol <- sequence subProblems'
         if (or . map isJust $ orsol) then
             return (Just $ procInfo':(head . catMaybes $ orsol))
           else
             return Nothing
           
evalF (Stage ioProof)    = join ioProof
evalF Success { procInfo = procInfo' } = return (Just [procInfo'])
evalF Fail {}       = return Nothing
evalF DontKnow {}   = return Nothing
evalF (MPlus p1 p2) = do { p1' <- p1
                         ; p2' <- p2
                         ; case p1' of
                             Nothing  -> case p2' of
                                           Nothing   -> return Nothing
                                           Just sol' -> return . Just $ sol'
                             Just sol -> return . Just $ sol
                         }
evalF MZero         = return Nothing