{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  MuTerm.Framework.PPr
-- Copyright   :  (c) muterm development team
-- License     :  see LICENSE
-- 
-- Maintainer  :  rgutierrez@dsic.upv.es
-- Stability   :  unstable
-- Portability :  non-portable 
--
-- This module manage the printing information.
--
-----------------------------------------------------------------------------

module MuTerm.Framework.Ppr (

-- * Exported classes

  Ppr (..)

-- * Exported modules

, module Ppr

) where

import Text.PrettyPrint.HughesPJ as Ppr -- (Doc, text, (<+>), int, comma, brackets, hsep, parens, punctuate, char, (<>), hcat, empty)

-----------------------------------------------------------------------------
-- Classes
-----------------------------------------------------------------------------

-- | The 'Ppr' class defines a 'Doc' representation of our datas.
class Ppr f where
    ppr      :: f -> Doc
    pprDebug :: f -> Doc
    pprDebug = ppr -- default definition

-- TODO: We have to add the monadic representation to take
-- into account the configuration of the output:
-- pprM :: (MonadReader ConfMuTerm, Ppr f) => f -> m Doc
-- pprI :: (?debug :: Bool, Ppr f) => f -> Doc
-----------------------------------------------------------------------------
-- Instances
-----------------------------------------------------------------------------

-- Ppr
{-
instance (Ppr a) => Ppr ([a]) where
    ppr []
        = text "Empty"
    ppr p
        = hsep . punctuate (char '\n') . map ppr $ p
    pprDebug
        = hsep . punctuate (char '\n') . map pprDebug

instance (Ppr a) => Ppr (Set a) where
    ppr p
        = if S.null p then
              text "Empty"
          else
              hsep . punctuate (char '\n') . map ppr . elems $ p
    pprDebug
        = hsep . punctuate (char '\n') . map pprDebug . elems
-}

--instance Ppr Char where ppr = char
instance Ppr Doc    where ppr d = d
instance Ppr Char   where ppr = char
instance Ppr String where ppr = text
instance Ppr Int    where ppr = Ppr.int
instance Ppr Integer where ppr = Ppr.integer
instance Ppr Bool where ppr = text . show

instance Ppr a => Ppr (Maybe a) where
    ppr Nothing  = text "Nothing"
    ppr (Just a) = text "Just" <+> ppr a
    pprDebug (Just a) = text "Just" <+> pprDebug a

instance Ppr () where ppr _ = empty
instance (Ppr a, Ppr b) => Ppr (a,b) where
    ppr (a,b) = parens (ppr a <> comma <> ppr b)
    pprDebug (a,b) = parens (pprDebug a <> comma <> pprDebug b)

instance (Ppr a, Ppr b, Ppr c) => Ppr (a,b,c) where
    ppr (a,b,c) = parens (ppr a <> comma <> ppr b <> comma <> ppr c)
    pprDebug (a,b,c) = parens (pprDebug a <> comma <> pprDebug b <> comma <> pprDebug c)

instance (Ppr a, Ppr b, Ppr c, Ppr d) => Ppr (a,b,c,d) where
    ppr (a,b,c,d) = parens (fsep $ punctuate comma [ppr a, ppr b, ppr c, ppr d])
    pprDebug (a,b,c,d) = parens (fsep $ punctuate comma [pprDebug a, pprDebug b, pprDebug c, pprDebug d])
