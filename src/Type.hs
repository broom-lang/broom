{-# LANGUAGE DeriveGeneric #-}

module Type (Type(..), MonoType(..), Row) where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)

import Util (Name)

data Type = TypeForAll [Name] MonoType
          | MonoType MonoType
          deriving (Show, Eq, Generic)

instance Hashable Type

data MonoType = TypeArrow MonoType MonoType
              | RecordType Row
              | DataType Name Row
              | TypeVar Name
              | PrimType String
              deriving (Show, Eq, Generic)

instance Hashable MonoType

type Row = [(String, MonoType)]
