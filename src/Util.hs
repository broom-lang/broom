{-# LANGUAGE DeriveGeneric #-}

module Util (Name, nameFromString, nameFromIntVar, nameToText) where

import Data.Monoid ((<>))
import Data.Text (Text, pack)
import Data.Hashable (Hashable)
import Control.Unification.IntVar (IntVar(..))
import GHC.Generics (Generic)
import Data.Text.Prettyprint.Doc (Pretty, pretty)

data Name = String String
          | Unique Int
          deriving (Show, Eq, Ord, Generic)

instance Hashable Name

nameFromString :: String -> Name
nameFromString = String

nameFromIntVar :: IntVar -> Name
nameFromIntVar (IntVar n) = Unique n

nameToText :: Name -> Text
nameToText = \case String s -> pack s
                   Unique n -> pack $ "$$" <> show n

instance Pretty Name where
    pretty = pretty . nameToText
