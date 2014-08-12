{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE KindSignatures, PolyKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric, DeriveDataTypeable #-}

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

ProofF(..), Proof, search

, SomeInfo (..), someInfo, Info, PrettyF
, IsMZero(..)

-- * Exported functions

, success, singleP, andP, dontKnow, refuted, mand, mprod
, isSuccess, runProof, runProofO

-- * Evaluation strategies
, parAnds
, sliceProof, unsafeSliceProof, simplifyProof
, pruneProof, pruneProofO
, pruneProofLazy, pruneProofLazyO
) where

import Control.Applicative
import Control.DeepSeq
import Control.Parallel.Strategies
import Control.Monad as M (MonadPlus(..), liftM, join)
import Control.Monad.Free (Free (..), foldFree, evalFree, mapFree, mapFreeM)
import Control.Monad.State.Strict (StateT, MonadState(..), evalState)
import Control.Monad.Zip
import Data.Foldable (Foldable(..))
import Data.Maybe (fromMaybe)
import Data.Monoid ()
import Data.Suitable
import Data.TagBits
import Data.Traversable as T (Traversable(..), foldMapDefault)
import Data.Typeable
import Data.Maybe (isNothing)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJClass
import Prelude.Extras

import qualified Data.Foldable as F

import Prelude as P hiding (pi)
import GHC.Generics(Generic)

import Debug.Hoed.Observe

-----------------------------------------------------------------------------
-- Proof Tree
-----------------------------------------------------------------------------

-- | Proof Tree constructors
data ProofF info (m :: * -> *) (k :: *) =
    And     {procInfo, problem :: !(SomeInfo info), subProblems::[k]}
  | Or      {procInfo, problem :: !(SomeInfo info), alternatives::m k}
  | Single  {procInfo, problem :: !(SomeInfo info), subProblem::k}
  | Success {procInfo, problem :: !(SomeInfo info)}
  | Refuted {procInfo, problem :: !(SomeInfo info)}
  | DontKnow{procInfo, problem :: !(SomeInfo info)}
  | Search !(m k)
  | MAnd  k k
  | MDone
  deriving Generic

-- | 'Proof' is a Free Monad. 'm' is the MonadPlus used for search
type Proof info m a = Free (ProofF info m) a

instance NFData a => NFData (ProofF info m a) where
  rnf (And _ _ pp) = rnf pp `seq` ()
  rnf Or{} = ()
  rnf (Single _ _ p) = rnf p `seq` ()
  rnf Success{} = ()
  rnf Refuted{} = ()
  rnf DontKnow{} = ()
  rnf Search{} = ()
  rnf (MAnd p1 p2) = rnf p1 `seq` rnf p2 `seq` ()
  rnf MDone = ()

instance (Observable1 m,  Observable(SomeInfo info)) => Observable1 (ProofF info m)

problemInfoF :: ProofF info m t -> Maybe (SomeInfo info)
problemInfoF (Search{}) = Nothing
problemInfoF (MAnd{})   = Nothing
problemInfoF (MDone{})  = Nothing
problemInfoF (other)    = Just (problem other)

problemInfo (Impure x)  = problemInfoF x
problemInfo  Pure{}     = Nothing

procInfoF :: ProofF info m t -> Maybe (SomeInfo info)
procInfoF (Search{}) = Nothing
procInfoF (MAnd{})   = Nothing
procInfoF (MDone{})  = Nothing
procInfoF (other)    = Just (procInfo other)

-- | Smart constructor for Search
search :: Monad m => m (Proof info m a) -> ProofF info m (Proof info m a)
search xx = Search (xx >>= flatten) where
  flatten (Impure(Search yy)) = yy
  flatten other = return other

-- ------------------------------
-- Parameterized super classes
-- ------------------------------
type Info f a = (Applicative f, Suitable f a, Ord a, Ord1 f, Typeable a, Typeable f)

-- | Pretty printing info witness
newtype PrettyF a = PrettyF a deriving (Functor, Pretty)
instance Applicative PrettyF where
  pure = PrettyF
  PrettyF f <*> PrettyF a = PrettyF (f a)

data instance Constraints PrettyF a = Pretty a => PrettyDict
instance Pretty p => Suitable PrettyF p where constraints = PrettyDict

-- -- | Tuples of information witnesses
-- data instance InfoConstraints (i,j) a = (:^:) (InfoConstraints i a) (InfoConstraints j a)
-- instance (Info i a, Info j a) => Info (i,j) a where
--   constraints = constraints :^: constraints

-- ------------------------
-- Existential Wrappers
-- ------------------------

-- | 'SomeInfo' existentially wraps a value together with a dictionary for a set of constraints
data SomeInfo f where
    SomeInfo :: (Typeable f, Typeable p, Suitable f p, Ord p) => f p -> SomeInfo f


instance Eq1 info => Eq (SomeInfo info) where
  SomeInfo a == SomeInfo b =
    case gcast b of
      Nothing -> False
      Just b' ->  a ==# b'

instance Ord1 info => Ord (SomeInfo info) where
  compare (SomeInfo a) (SomeInfo b) =
    case gcast b of
      Nothing -> compare (typeOf a) (typeOf b)
      Just b' -> compare1 a b'

instance Pretty (SomeInfo PrettyF) where
   pPrint (SomeInfo p) = withConstraintsOf p $ \PrettyDict -> pPrint p


-- Tuple instances

-- instance Pretty (SomeInfo (PrettyI, a)) where
--     pPrint (SomeInfo (p::p)) = withInfoOf p $ \(PrettyInfo :^: _) -> pPrint p

-- instance Pretty (SomeInfo (a,PrettyI)) where
--     pPrint (SomeInfo (p::p)) = withInfoOf p $ \((x::InfoConstraints a p) :^: PrettyInfo) -> pPrint p

-----------------------------------------------------------------------------
-- Instances
-----------------------------------------------------------------------------

instance Monad m => Functor (ProofF info m) where
  fmap f (And pi p kk)   = And pi p (fmap f kk)
  fmap f (Single pi p k) = Single pi p (f k)
  fmap _ (Success pi p)  = Success pi p
  fmap _ (Refuted pi p)  = Refuted pi p
  fmap _ (DontKnow pi p) = DontKnow pi p
  fmap f (Or pi p mk)    = Or pi p (liftM f mk)
  fmap f (Search mk)     = Search  (liftM f mk)
  fmap f (MAnd k1 k2)    = MAnd (f k1) (f k2)
  fmap _f MDone          = MDone

instance (Monad m, Traversable m) => Foldable (ProofF info m) where foldMap = T.foldMapDefault

instance (Monad m, Traversable m) => Traversable (ProofF info m) where
  traverse f (And pi p kk)   = And pi p <$> traverse f kk
  traverse f (Single pi p k) = Single pi p <$> f k
  traverse _ (Success pi p)  = pure $ Success pi p
  traverse _ (Refuted pi p)  = pure $ Refuted pi p
  traverse _ (DontKnow pi p) = pure $ DontKnow pi p
  traverse f (Search mk)     = Search <$> traverse f mk
  traverse f (Or pi p mk)    = Or pi p <$> traverse f mk
  traverse f (MAnd k1 k2)    = MAnd <$> f k1 <*> f k2
  traverse _f MDone          = pure MDone


-- MonadPlus

instance MonadPlus m => MonadPlus (Free (ProofF info m)) where
    mzero       = Impure (Search mzero)
    mplus (Impure(Search m1)) (Impure(Search m2)) = Impure $ search $ mplus m1 m2
--    mplus (Impure DontKnow{}) p2 = p2
--    mplus p1 (Impure DontKnow{}) = p1
    mplus !p1 p2 = Impure $ search (mplus (return p1) (return p2))

-- Show
-----------------------------------------------------------------------------
-- Smart Constructors
-----------------------------------------------------------------------------

-- | Return a success node
success :: (Monad m, Info info p, Info info problem) => p -> problem -> Proof info m b
success pi p0 = Impure (Success (someInfo pi) (someProblem p0))

-- | Return a refuted node
refuted :: (Monad m, Info info p, Info info problem) => p -> problem -> Proof info m b
refuted pi p0 = Impure (Refuted (someInfo pi) (someProblem p0))

-- | Returns a don't know node
dontKnow :: (Monad m, Info info p, Info info problem) => p -> problem -> Proof info m b
dontKnow pi p0 = Impure (DontKnow (someInfo pi) (someProblem p0))

-- | Return a new single node
singleP :: (Monad m, Info info p, Info info problem) => p -> problem -> b -> Proof info m b
singleP pi p0 p = Impure (Single (someInfo pi) (someProblem p0) (return p))

-- | Return a list of nodes
andP :: (Monad m, Info info p, Info info problem) => p -> problem -> [b] -> Proof info m b
andP pi p0 [] = success pi p0
andP pi p0 pp = Impure (And (someInfo pi) (someProblem p0) (map return pp))

mand :: Monad m => Proof info m a -> Proof info m a -> Proof info m a
mand a b = Impure (MAnd a b)

mprod :: Monad m => [Proof info m a] -> Proof info m a
mprod = P.foldr mand (Impure MDone) where
  mand a (Impure MDone) = a
  mand a b = Impure (MAnd a b)

-- ---------
-- Functions
-- ---------
xx `at` k = fromMaybe (error "at") (lookup k xx)

-- | Pack the proof information
someInfo :: (Typeable p, Info f p) => p -> SomeInfo f
someInfo = SomeInfo . pure

-- | Pack the problem
someProblem :: (Typeable p, Info f p) => p -> SomeInfo f
someProblem = SomeInfo . pure

-- | Obtain the solution, collecting the proof path in the way
evalSolF' :: (MonadPlus mp) => Observer -> ProofF info mp (mp(Proof info t ())) -> mp (Proof info t ())
evalSolF' _ Refuted{..}    = return (Impure Refuted{..})
evalSolF' _ DontKnow{}     = mzero
evalSolF' _ MDone          = return (Impure MDone)
evalSolF' _ Success{..}    = return (Impure Success{..})
evalSolF' _ (Search mk)    = join mk
evalSolF' _ (And pi pb []) = return (Impure $ Success pi pb)
evalSolF' _ (And pi pb ll) = (Impure . And pi pb) `liftM` P.sequence ll
evalSolF' _ (Or  pi pb ll) = (Impure . Single pi pb) `liftM` join ll
evalSolF' _ (MAnd  p1 p2)  = p1 >>= \s1 -> p2 >>= \s2 ->
                             return (Impure $ MAnd s1 s2)
evalSolF' _ (Single pi pb p) = (Impure . Single pi pb) `liftM` p

class MonadPlus mp => IsMZero mp where isMZero :: mp a -> Bool
instance IsMZero []    where isMZero = null
instance IsMZero Maybe where isMZero = isNothing

-- | Evaluate if proof is success
isSuccess :: IsMZero mp => Proof info mp a -> Bool
isSuccess = not . isMZero . foldFree (const mzero) (evalSolF' nilObserver)

data EmptyF a deriving (Functor, Foldable, Traversable, Generic)

instance Applicative EmptyF
instance Monad EmptyF
instance MonadPlus EmptyF
instance IsMZero EmptyF where isMZero _ = True
instance Observable1 EmptyF

-- | Apply the evaluation returning the relevant proof subtree
runProof  :: (MonadPlus mp
             ) => Proof info mp a -> mp (Proof info EmptyF ())
runProof = foldFree (const mzero) (evalSolF' nilObserver)
runProofO :: (Observable (SomeInfo info), Observable1 mp, MonadPlus mp
             ) => Observer -> Proof info mp a -> mp (Proof info EmptyF ())
runProofO (O o oo) = foldFree (const mzero) (oo "evalSolF" evalSolF')

-- Evaluation Strategies
-- Evaluate and branches in parallel
parAnds :: Strategy (Proof info m a)
parAnds (Pure p) = return (Pure p)
parAnds (Impure i) = liftM Impure (f i) where
   f (And    pi p pp)= And    pi p <$> parList parAnds pp
   f (Single pi p k) = Single pi p <$> parAnds k
   f (MAnd p1 p2)    = MAnd <$> rpar (p1 `using` parAnds) <*> rpar (p2 `using` parAnds)
   f it = return it

-- | Approximately slices a proof to keep only the evaluated branches.
--   Useful for things like displaying a failed proof.
sliceProof,unsafeSliceProof :: (Functor mp, Foldable mp, IsMZero mp) => Proof info mp a -> Proof info mp a
sliceProof = mapFree f where
    f (And p pi pp) = And p pi $ takeWhileAndOneMore isSuccess pp
    f (MAnd  p1 p2) = if not(isSuccess p1) then Search (return p1) else (MAnd p1 p2)
    f (Or  p pi pp) = Or  p pi $ takeWhileMP (not.isSuccess) pp
    f (Search m)    = search   $ takeWhileMP (not.isSuccess) m
    f x = x

    takeWhileAndOneMore _ []     = []
    takeWhileAndOneMore f (x:xs) = if f x then x : takeWhileAndOneMore f xs else [x]

-- Eliminate intermediate steps that do not improve the problem
simplifyProof :: (Monad m, IsMZero m, Traversable m, Typeable info, Eq1 info) =>
                 Proof info m a -> Proof info m a
simplifyProof = removeEmpty . removeIdem

pruneProof :: ( MonadPlus m, Traversable m, Ord1 info
              , Observable (SomeInfo info), Observable1 Set.Set, Observable a, Observable1 m
              ) => Proof info m a -> Proof info m a
pruneProof = pruneProofO nilObserver
-- Eliminate duplicate subproofs
pruneProofO :: ( MonadPlus m, Traversable m, Ord1 info
               , Observable (SomeInfo info), Observable1 Set.Set, Observable a, Observable1 m
               ) => Observer -> Proof info m a -> Proof info m a
pruneProofO (O o oo) = (`evalState` Set.empty) . mapFreeM (oo "f" f) where
  f (O o oo) x@Success{}  = return x
  f (O o oo) x@DontKnow{} = return x
  f (O o oo) x@Refuted{}  = return x
  f (O o oo) x@And{}      = return x
--  f (O o oo) x@Single{}   = return x -- this case shouldn't be here, but..
  f (O o oo) x | Just pi <- problemInfoF x
               , Just procI <- procInfoF x
               = do
    seen <- get
    if o "member" Set.member (pi, procI) seen
       then return $ Search mzero
       else do
         put (Set.insert (pi,procI) seen)
         return x
  f _ x = return x

{- Circular version of pruneProof, as unfortunately the monadic one makes the tree strict and therefore is useless for our purposes.
   Here we make use of circularity to compute a map from (problemInfo, procInfo) to a position in the tree,
   that we then use to remove duplicates from the tree.
   But instead of doing it in two passes, we do it in the same one, which means we don't have to force the entire tree.
 -}


pruneProofLazy :: ( Eq1 info, MonadZip m
                  , Observable(SomeInfo info), Observable a, Observable1 m
                  ) => (forall x. m x -> [x])
                    -> Free (ProofF info m) a
                    -> Free (ProofF info m) a
pruneProofLazy x = pruneProofLazyO nilObserver x

pruneProofLazyO :: ( Eq1 info, MonadZip m
                   , Observable(SomeInfo info), Observable a, Observable1 m
                   ) => Observer
                     -> (forall x. m x -> [x])
                     -> Free (ProofF info m) a
                     -> Free (ProofF info m) a
pruneProofLazyO (O o oo) run x =
  let (seen, res) = foldFree (\v -> ([], Pure v)) (oo "f" f seen) x in res
 where
  f _ _    (Success  pi p)                       = ([], Impure(Success  pi p))
  f _ _    (DontKnow pi p)                       = ([], Impure(DontKnow pi p))
  f _ _    (Refuted  pi p)                       = ([], Impure(Refuted  pi p))

  f _ seen (And      pi p (unzip -> (seens,xx))) = ( ((pi,p), Impure(And pi p xx)) : concat seens
                                                   , seen `at` (pi,p))
  f _ seen (Or       pi p (munzip -> (seens,xx))) = ( ((pi,p), Impure(Or pi p xx)) : concat(run seens)
                                                   , seen `at` (pi,p))
  f _ seen (Single   pi p (seens,it))             = ( ((pi,p), Impure(Single pi p it)) : seens
                                                   , seen `at` (pi,p))
  f _ _    (Search   (munzip -> (seens, xx)))     = ( concat(run seens), Impure(Search xx))
  f _ _     MDone                                = ([], Impure MDone)
  f _ _    (MAnd (seens1, x1) (seens2, x2))      = ( seens1 ++ seens2, Impure(MAnd x1 x2 ))


instance Monad m => Observable1 (StateT s m) where
  observer1 comp p = do
    res <- comp
    send "<State>" (return return << res) p

deriving instance Generic (Free f v)
instance Observable1 f => Observable1 (Free f) where
  observer1 (Pure t)   = Pure . observer t
  observer1 (Impure t) = Impure . observer t

removeEmpty :: (IsMZero m, Traversable m) => Proof info m a -> Proof info m a
removeEmpty = Impure . search . foldFree (return . Pure) f where
  f (Search k) =
    let filtered = filterMP (not.isMZero) k in
    case F.toList filtered of
      []  -> mzero
      [x] -> x
      _   -> return $ Impure $ search $ join $ filtered
  f other = fmap Impure $ T.sequence other

removeIdem x = foldFree (\v _ -> Pure v) f x (problemInfo x)
 where
  f(And _ pi [subp]) parent
    | Just pi == parent = subp parent
  f(And p pi pp) _parent = Impure $ And p pi (map ($ Just pi) pp)
  f(Single p pi k) parent
    | Just pi == parent = k parent
    | otherwise = Impure $ Single p pi (k $ Just pi)

  f(Or p pi pp) _    = Impure $ Or p pi (liftM ($ Just pi) pp)
  f MDone _          = Impure MDone
  f(Search k) parent = Impure $ search (liftM ($ parent) k)
  f(DontKnow p pi) _ = Impure $ DontKnow p pi
  f(Success p pi)  _ = Impure $ Success p pi
  f(Refuted p pi)  _ = Impure $ Refuted p pi
  f(MAnd p1 p2) parent = Impure $ MAnd (p1 parent) (p2 parent)

-- | Slices a proof to keep only the evaluated branches.
--   Uses the impure 'unsafeIsEvaluated' function from the tag-bits package to discern evaluated subtrees.
--   Regardless its name, 'unsafeSliceProof' is actually safe.
unsafeSliceProof = evalFree Pure (Impure . f) where
    f (And p pi pp) = let pp' = filterMP unsafeIsEvaluated pp in
                      And p pi $ map unsafeSliceProof $ takeWhileAndOneMore isSuccess pp'
    f (MAnd  p1 p2) = if not(isSuccess p1)
                       then Search (return $ sliceProof p1)
                      else (MAnd (sliceProof p1) (sliceProof p2))
    f (Or  p pi pp) = Or  p pi $ fmap unsafeSliceProof $ takeWhileMP (unsafeIsEvaluated .&. not.isSuccess) pp
    f (Search m)    = search   $ fmap unsafeSliceProof $ takeWhileMP (unsafeIsEvaluated .&. not.isSuccess) m
    f x = x

    takeWhileAndOneMore _ []     = []
    takeWhileAndOneMore f (x:xs) = if f x then x : takeWhileAndOneMore f xs else [x]
    infixr 3 .&.
    f .&. g = \x -> f x && g x

filterMP, takeWhileMP :: (Foldable m, MonadPlus m) => (a -> Bool) -> m a -> m a
takeWhileMP p = F.foldr f mzero
  where
    f x acc  = if p x then return x `mplus` acc else mzero

filterMP p = F.foldr f mzero where f x acc = if p x then return x `mplus` acc else acc
