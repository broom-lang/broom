{-# LANGUAGE DeriveGeneric #-}

module Util (Name, nameFromString) where

import Data.Unique (Unique, newUnique, hashUnique)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)

data Name = String String
          | Unique String Unique
          deriving (Eq, Ord, Generic)

instance Show Name where
    show (String s) = s
    show (Unique s n) = s ++ show (hashUnique n)

instance Hashable Name

nameFromString :: String -> Name
nameFromString = String

freshName :: String -> IO Name
freshName s = Unique s <$> newUnique
