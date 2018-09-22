{-# LANGUAGE TypeApplications, DeriveGeneric #-}

module Util (Name) where

import Data.Semigroup ((<>))
import Data.Convertible (Convertible, safeConvert, convert)
import Data.Text (Text, pack, unpack)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Data.Text.Prettyprint.Doc (Pretty, pretty)

data Name = String Text
          | Unique Int
          deriving (Eq, Ord, Generic)

instance Hashable Name

instance Show Name where
    show (String t) = unpack t
    show (Unique n) = "$$" <> show n

instance Convertible Text Name where
    safeConvert = pure . String

instance Convertible Name Text where
    safeConvert (String s) = pure s
    safeConvert (Unique n) = pure (pack ("$$" <> show n))

instance Pretty Name where
    pretty = pretty . convert @Name @Text
