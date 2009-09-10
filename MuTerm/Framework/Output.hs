{-# LANGUAGE FlexibleContexts,FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
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
import Data.List
import Data.HashTable (hashString)

import qualified Text.XHtml as H
import Text.XHtml hiding (text)

import MuTerm.Framework.DotRep
import MuTerm.Framework.Ppr as Doc hiding (Style)
import MuTerm.Framework.Problem
import MuTerm.Framework.Proof

-- ----
-- Text
-- ----

instance (Ppr a) => Ppr (ProofF mp a) where ppr = pprProofF
pprProofF = f where
      f Success{..} =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo $$
        text ("RESULT: Problem solved succesfully")
      f Fail{..} =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo  $$
        text ("RESULT: Problem could not be solved.")
      f DontKnow{..} =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo  $$
        text ("RESULT: Don't know.")
{-
      f (Or proc prob sub) =
        ppr prob $$
        text "PROCESSOR: " <> ppr proc $$
        text ("Problem was translated to " ++ show (length sub) ++ " equivalent problems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr sub)
-}
      f (And proc prob sub)
       | length sub > 1 =
        ppr prob $$
        text "PROCESSOR: " <> ppr proc $$
        text ("Problem was divided in " ++ show (length sub) ++ " subproblems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr sub)
       | otherwise =
        ppr prob $$
        text "PROCESSOR: " <> ppr proc $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr sub)
      f (Single{..}) =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo $$
        nest 8 (ppr subProblem)
      f (MAnd p1 p2) =
        text ("Problem was divided in 2 subproblems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr [p1,p2])
      f MDone = text "Done"

--------------
-- HTML
-------------

instance HTML Doc where toHtml = toHtml . show

data Unit1 a
instance Monad Unit1

instance (Ppr a, Ord a) => HTML (Proof Unit1 a) where
   toHtml = foldFree (\prob -> p<<(ppr prob $$ text "RESULT: not solved yet")) work where
    work DontKnow{}  = toHtml  "Don't know"
    work Success{..} =
       p
        << problem  +++ br +++
           procInfo +++ br +++
           divyes

    work Fail{..} =
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


-- ----
-- Dot
-- ----

instance (IsDPProblem typ, Ppr rules) => DotRep (DPProblem typ [rules]) where
  dot p = Text rep atts where
    atts = [ Shape BoxShape
           , Style (Stl Bold Nothing)
           , FontName "monospace"
           , FontSize 10
           , Margin (PVal (PointD 0.2 0.2))]
    rep = vcat
     [parens( text "PAIRS" $$
             nest 1 (vcat $ map ppr (getP p)))
     ,parens( text "RULES" $$
             nest 1 (vcat $ map ppr (getR p)))
     ]

