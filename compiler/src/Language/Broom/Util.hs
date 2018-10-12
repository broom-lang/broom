{-# LANGUAGE TypeApplications, DeriveGeneric #-}

module Language.Broom.Util (Name, fresh, gensym, (<&>)) where

import Data.Data (Data, Typeable)

import Data.Semigroup ((<>))
import Data.Convertible (Convertible, safeConvert, convert)
import Data.String (IsString, fromString)
import Data.Text (Text, pack, unpack)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Data.Text.Prettyprint.Doc (Pretty, pretty)
import Control.Eff (Eff, Member)
import Control.Eff.State.Strict (State, get, modify)

data Name = String Text
          | Unique Int
          | Uniquefied Text Int
          deriving (Eq, Ord, Generic, Data, Typeable)

instance Hashable Name

instance IsString Name where
    fromString = String . pack

instance Show Name where
    show (String t) = unpack t
    show (Unique n) = "$$" <> show n
    show (Uniquefied t n) = unpack t <> "__" <> show n

instance Convertible Text Name where
    safeConvert = pure . String

instance Convertible Name Text where
    safeConvert (String s) = pure s
    safeConvert (Unique n) = pure (pack ("$$" <> show n))
    safeConvert (Uniquefied t n) = pure (t <> "__" <> pack (show n))

instance Pretty Name where
    pretty = pretty . convert @Name @Text

fresh :: Member (State Int) r => Eff r Int
fresh = do { res <- get; modify (\(counter :: Int) -> counter + 1); pure res }

gensym :: Member (State Int) r => Name -> Eff r Name
gensym = \case
    String t -> Uniquefied t <$> fresh
    Unique _ -> Unique <$> fresh
    Uniquefied t _ -> Uniquefied t <$> fresh

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap
