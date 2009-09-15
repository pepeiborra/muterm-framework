-----------------------------------------------------------------------------
-- |
-- Module      :  MuTerm.Framework.DotRep
-- Copyright   :  (c) muterm development team
-- License     :  see LICENSE
--
-- Maintainer  :  jiborra@dsic.upv.es
-- Stability   :  unstable
-- Portability :  non-portable
--
--
-----------------------------------------------------------------------------

module MuTerm.Framework.DotRep
    ( module MuTerm.Framework.DotRep,
      module Data.GraphViz.Attributes) where

import qualified Data.Graph
import Data.GraphViz.Attributes
import Data.Graph.Inductive
import Data.Graph.Inductive.Tree
import Text.PrettyPrint.HughesPJClass

class DotRep a where
   dot, dotSimple :: a -> DotGr
   dotSimple = dot
   dot = dotSimple

type DotGr = DotGrF (Gr [Attribute] [Attribute])
data DotGrF a = Text Doc [Attribute]
              | Nodes { nodes :: a
                      , attributes :: [Attribute]
                      , incoming, outgoing :: Node}

defaultDot x = Text (pPrint x) []

mkColor x = [ColorName x]
label l = Label (StrLabel ('\"' : renderDot l ++ "\""))

renderDot :: Doc -> String
renderDot = concatMap escapeNewLines . (`shows` "\\l")
      where
        escapeNewLines '\n' = "\\l"
        escapeNewLines c    = [c]
