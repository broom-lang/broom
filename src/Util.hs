{-# LANGUAGE DeriveGeneric #-}

module Util (Name, nameFromString, nameFromIntVar) where

import Data.Hashable (Hashable)
import Control.Unification.IntVar (IntVar(..))
import GHC.Generics (Generic)

data Name = String String
          | Unique Int
          deriving (Show, Eq, Ord, Generic)

instance Hashable Name

nameFromString :: String -> Name
nameFromString = String

nameFromIntVar :: IntVar -> Name
nameFromIntVar (IntVar n) = Unique n
