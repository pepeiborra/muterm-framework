{-# LANGUAGE FlexibleContexts,FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ExistentialQuantification #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  MuTerm.Framework.Output
-- Copyright   :  (c) muterm development team
-- License     :  see LICENSE
--
-- Maintainer  :  jiborra@dsic.upv.es
-- Stability   :  unstable
-- Portability :  non-portable
--
-- This module contains the proof functor.
--
-----------------------------------------------------------------------------

module MuTerm.Framework.Output where

import Control.Monad.Free
import Data.Foldable (Foldable, toList)
import Data.List
-- import Data.HashTable (hashString)

import qualified Text.XHtml as H
import Text.XHtml hiding (text)

import Text.PrettyPrint.HughesPJClass as Doc hiding (Style)
import MuTerm.Framework.Problem
import MuTerm.Framework.Proof

-- ----
-- Text
-- ----

instance (Pretty a) => Pretty (ProofF PrettyInfo mp a) where pPrint = pprProofF
instance (Pretty a, Pretty (SomeInfo info)) => Pretty (ProofF info mp a) where pPrint = pprProofF

pprProofF = f where
      f Success{..} =
        pPrint problem $$
        text "PROCESSOR: " <> pPrint procInfo $$
        text ("RESULT: Problem solved succesfully")
      f Refuted{..} =
        pPrint problem $$
        text "PROCESSOR: " <> pPrint procInfo  $$
        text ("RESULT: Termination could be refuted.")
      f DontKnow{..} =
        pPrint problem $$
        text "PROCESSOR: " <> pPrint procInfo  $$
        text ("RESULT: Don't know.")
{-
      f (Or proc prob sub) =
        pPrint prob $$
        text "PROCESSOR: " <> pPrint proc $$
        text ("Problem was translated to " ++ show (length sub) ++ " equivalent problems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map pPrint sub)
-}
      f (And proc prob sub)
       | length sub > 1 =
        pPrint prob $$
        text "PROCESSOR: " <> pPrint proc $$
        text ("Problem was divided in " ++ show (length sub) ++ " subproblems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map pPrint sub)
       | otherwise =
        pPrint prob $$
        text "PROCESSOR: " <> pPrint proc $$
        nest 8 (vcat $ punctuate (text "\n") $ map pPrint sub)
      f (Single{..}) =
        pPrint problem $$
        text "PROCESSOR: " <> pPrint procInfo $$
        nest 8 (pPrint subProblem)
      f (MAnd p1 p2) =
        text ("Problem was divided in 2 subproblems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map pPrint [p1,p2])
      f MDone = text "Done"
      f (Search sub) = text "Trying something different"

-- | Gives more information on the attempted failed branches
pprProofFailures = foldFree (const Doc.empty) f . sliceProof where
      f Success{..} =
        pPrint problem $$
        text "PROCESSOR: " <> pPrint procInfo $$
        text ("RESULT: Problem solved succesfully")
      f Refuted{..} =
        pPrint problem $$
        text "PROCESSOR: " <> pPrint procInfo  $$
        text ("RESULT: Termination could be refuted.")
      f DontKnow{..} =
        pPrint problem $$
        text "PROCESSOR: " <> pPrint procInfo  $$
        text ("RESULT: Don't know.")
{-
      f (Or proc prob sub) =
        pPrint prob $$
        text "PROCESSOR: " <> pPrint proc $$
        text ("Problem was translated to " ++ show (length sub) ++ " equivalent problems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map pPrint sub)
-}
      f (And proc prob sub)
       | length sub > 1 =
        pPrint prob $$
        text "PROCESSOR: " <> pPrint proc $$
        text ("Problem was divided in " ++ show (length sub) ++ " subproblems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ sub)
       | otherwise =
        pPrint prob $$
        text "PROCESSOR: " <> pPrint proc $$
        nest 8 (vcat $ punctuate (text "\n") $ sub)
      f (Single{..}) =
        pPrint problem $$
        text "PROCESSOR: " <> pPrint procInfo $$
        nest 8 subProblem
      f (MAnd p1 p2) =
        text ("Problem was divided in 2 subproblems.") $$
        nest 8 (p1 $$ p2)
      f MDone = text "Done"
      f (Search sub) = vcat . intersperse (text "Trying something different") . toList $ sub

--------------
-- HTML
-------------

-- | Dummy default instance
-- instance Pretty a => HTML a where toHtml = toHtml . show . pPrint

-- | HTML instance witness
data HTMLInfo
instance HTML p => Info HTMLInfo p where
  data InfoConstraints HTMLInfo p = HTML p => HTMLInfo
  constraints = HTMLInfo

instance HTML (SomeInfo HTMLInfo) where
    toHtml (SomeInfo p) = withInfoOf p $ \HTMLInfo -> toHtml p

instance HTML Doc where toHtml = toHtml . show


instance (Pretty a, Ord a, Monad m) => HTML (Proof HTMLInfo m a) where
  toHtml = toHtmlProof

instance (Pretty a, Ord a, Monad m, HTML (SomeInfo info)) => HTML (Proof info m a) where
  toHtml = toHtmlProof

toHtmlProof = foldFree (\prob -> p<<(pPrint prob $$ text "RESULT: not solved yet")) work where
    work DontKnow{}  = toHtml  "Don't know"
    work Success{..} =
       p
        << problem  +++ br +++
           procInfo +++ br +++
           divyes

    work Refuted{..} =
        p
        << problem  +++ br +++
           procInfo +++ br +++
           divmaybe
{-
    work Or{..} =
        p
        << problem +++ br +++
           procInfo +++ br +++
           "Problem was translated to " +++ show(length alternatives) +++ " equivalent alternatives" +++ br +++
           unordList alternatives
-}
    work (And proc prob sub) =
        p
        << prob +++ br +++
           proc +++ br +++
--           "Problem was divided in " +++ show(length sub) +++ " subproblems" +++ br +++
           unordList sub
    work (MAnd p1 p2) =
        p
        << unordList [p1,p2]
    work MDone = noHtml -- toHtml "RESULT: D"
    work Single{..} = p
                    << problem +++ br +++ procInfo +++ br +++ subProblem


divi ident = H.thediv ! [H.theclass ident]
spani ident = H.thespan ! [H.theclass ident]
divresult = spani "result" << "RESULT: "
divyes    = divresult +++ spani "yes" << "YES. "
divmaybe  = divresult +++ spani "maybe" << "Fail. "

