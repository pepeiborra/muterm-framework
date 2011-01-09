{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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

import Control.Applicative
import qualified Data.Graph
import Data.GraphViz.Attributes
import Data.Graph.Inductive
import Data.Graph.Inductive.Tree
import Data.Suitable
import Text.PrettyPrint.HughesPJClass

import MuTerm.Framework.Proof

class DotRep a where
   dot, dotSimple :: a -> DotGr
   dotSimple = dot
   dot = dotSimple

-- | Dummy default instance
instance Pretty a => DotRep a where dot x = Text (pPrint x) []

type DotGr = DotGrF (Gr [Attribute] [Attribute])
data DotGrF a = Text Doc [Attribute]
              | Nodes { nodes :: a
                      , legend :: Maybe (Doc,[Attribute])
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

-- ------------------------
-- *Info constraints
-- ------------------------

-- | Dot instance witness
newtype DotF a = DotF a deriving (Functor, DotRep, Pretty)

instance Applicative DotF where
  pure = DotF
  DotF f <*> DotF a = DotF (f a)

data instance Constraints DotF a = DotRep a => DotConstraint
instance DotRep p => Suitable DotF p where constraints = DotConstraint

instance DotRep (SomeInfo DotF) where
    dot (SomeInfo p) = withConstraintsOf p $ \DotConstraint -> dot p
    dotSimple (SomeInfo p) = withConstraintsOf p $ \DotConstraint -> dotSimple p



-- Tuple instances

-- instance DotRep (SomeInfo (DotInfo, a)) where
--     dot (SomeInfo (p::p)) = withInfoOf p $ \(DotInfo :^: (_::InfoConstraints a p)) -> dot p
--     dotSimple (SomeInfo (p::p)) = withInfoOf p $ \(DotInfo :^: (_::InfoConstraints a p)) -> dotSimple p

-- instance DotRep (SomeInfo (a,DotInfo)) where
--     dot (SomeInfo (p::p)) = withInfoOf p $ \((x::InfoConstraints a p) :^: DotInfo) -> dot p
--     dotSimple (SomeInfo (p::p)) = withInfoOf p $ \((x::InfoConstraints a p) :^: DotInfo) -> dotSimple p
