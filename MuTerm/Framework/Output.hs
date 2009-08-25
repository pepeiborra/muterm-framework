{-# LANGUAGE FlexibleContexts,FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
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

instance (Ppr a) => Ppr (ProofF a) where ppr = pprProofF
pprProofF = f where
      f MZero = empty -- text "don't know"
      f Success{..} =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo $$
        text ("RESULT: Problem solved succesfully") $$
        proofTail procInfo
      f Fail{..} =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo  $$
        text ("RESULT: Problem could not be solved.") $$
        proofTail procInfo
      f DontKnow{..} =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo  $$
        text ("RESULT: Don't know.") $$
        proofTail procInfo

      f (Or proc prob sub) =
        ppr prob $$
        text "PROCESSOR: " <> ppr proc $$
        text ("Problem was translated to " ++ show (length sub) ++ " equivalent problems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr sub)

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
      f (MPlus p1 p2) =
        text ("There is a choice.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr [p1,p2])
      f (MAnd p1 p2) =
        text ("Problem was divided in 2 subproblems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr [p1,p2])
      f MDone = text "Done"
      f (Stage p) = ppr p

      proofTail :: SomeInfo -> Doc
--      proofTail (SomeInfo (External _ (find isOutputTxt -> Just (OutputTxt (unpack -> txt)))))
--                  = text ("Output: ") <> (vcat . map text . lines) txt
      proofTail _ = Doc.empty

--------------
-- HTML
-------------

instance HTML Doc where toHtml = toHtml . show
--instance HTML a => HTMLTABLE a where cell = cell . toHtml
{-
instance (HTML (TRS typ)) => HTML (DPProblem typ) where
    toHtml (Rewriting trs)      = toHtmlProblem1 "REW" "Direct Rewriting Termination" trs
    toHtml (DPFProblem trs dps) = toHtmlProblem2 "DP"  "DP Problem"                   trs dps
    -- TODO add all the relevant instances

toHtmlProblem1 c title trs =
        H.table ! [H.theclass c] << (
            H.td ! [H.theclass "problem"] << H.bold << title </>
            H.td ! [H.theclass "TRS_TITLE" ] << "Rules"</> toTable trs)

toHtmlProblem2 c title trs dps =
        H.table ! [H.theclass c] << (
            H.td ! [H.theclass "problem"] << H.bold << title </>
            H.td ! [H.theclass "TRS_TITLE" ] << "Rules" </> toTable trs </>
            H.td ! [H.theclass "DPS" ] << "Dependency Pairs" </> toTable dps)

toTable = cell . toHtml
-}

instance (Ppr a, Ord a) => HTML (Proof a) where
   toHtml = foldFree (\prob -> p<<(ppr prob $$ text "RESULT: not solved yet")) work where
    work MZero       = toHtml  "Don't know"
    work DontKnow{}  = toHtml  "Don't know"
    work Success{..} =
       p
        << problem  +++ br +++
           procInfo +++ br +++
           divyes +++ detailResult procInfo

    work Fail{..} =
        p
        << problem  +++ br +++
           procInfo +++ br +++
           divmaybe +++ detailResult procInfo
--           divmaybe +++ thickbox res << spani "seeproof" << "(see failure)"

    work Or{..} =
        p
        << problem +++ br +++
           procInfo +++ br +++
           "Problem was translated to " +++ show(length subProblems) +++ " equivalent alternatives" +++ br +++
           unordList subProblems

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
    work (MPlus    _ p2)  = p2 -- If we see the choice after simplifying, it means that none was successful
    work (Stage p)= p
    work Single{..} = p
                    << problem +++ br +++ procInfo +++ br +++ subProblem

    detailResult :: SomeInfo -> Html
--    detailResult (SomeInfo (External _ (find isOutputHtml -> Just (OutputHtml (unpack -> output))))) =
--       thickbox output << spani "seeproof" << "(see proof)"
    detailResult _ = noHtml


divi ident = H.thediv ! [H.theclass ident]
spani ident = H.thespan ! [H.theclass ident]
divresult = spani "result" << "RESULT: "
divyes    = divresult +++ spani "yes" << "YES. "
divmaybe  = divresult +++ spani "maybe" << "Fail. "
thickbox thing c | label <- hashHtml thing =
         thediv ! [H.identifier ("tb"++label), H.thestyle "display:none"] << p << thing +++
         H.hotlink ("#TB_inline?height=600&width=600&inlineId=tb" ++ label) ! [theclass "thickbox"] << c

hashHtml = show . abs . hashString . H.renderHtml


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

