{-# LANGUAGE FlexibleInstances #-}
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
, Output(..)

-- * Exported modules

, module Text.PrettyPrint.HughesPJ

) where

import Text.PrettyPrint.HughesPJ (Doc, text, (<+>), int, comma, brackets, hsep, parens, punctuate, char, (<>), hcat, empty)
import Data.Set as S (Set, elems, null)
import Control.Monad.Reader (MonadReader (..))


-- | Different types of 'Output'.
data Output = Plain
            | HTML
            | XML
              deriving Show
-----------------------------------------------------------------------------
-- Classes
-----------------------------------------------------------------------------

-- | The 'Ppr' class defines a 'Doc' representation of our datas.
class Ppr f where
    pprBase  :: f -> Doc
    pprDebug :: f -> Doc
    ppr      :: f -> Doc
    pprFormat :: Output -> f -> Doc
    pprDebug = pprBase      -- default definition
    ppr      = pprBase      -- default definition
    pprFormat _ = pprBase      -- default definition
    pprBase  = pprFormat Plain   -- default definition

-- TODO: We have to add the monadic representation to take
-- into account the configuration of the output:
-- pprM :: (MonadReader ConfMuTerm, Ppr f) => f -> m Doc
-- pprI :: (?debug :: Bool, Ppr f) => f -> Doc

-----------------------------------------------------------------------------
-- Instances
-----------------------------------------------------------------------------

-- Ppr

instance (Ppr a) => Ppr ([a]) where
    pprBase []
        = text "Empty"
    pprBase p
        = hsep . punctuate (char '\n') . map pprBase $ p
    pprDebug
        = hsep . punctuate (char '\n') . map pprDebug

instance (Ppr a) => Ppr (Set a) where
    pprBase p
        = if S.null p then
              text "Empty"
          else
              hsep . punctuate (char '\n') . map pprBase . elems $ p
    pprDebug
        = hsep . punctuate (char '\n') . map pprDebug . elems
