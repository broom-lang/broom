module Ast (Expr(..), Type(..), Atom(..), Const(..)) where

import Data.Unique (Unique, hashUnique)

instance Show Unique where
    show uq = "t" ++ show (hashUnique uq)

data Expr t = Lambda String t (Expr t)
            | App (Expr t) (Expr t)
            | Let String t (Expr t) (Expr t)
            | Record [(String, Expr t)]
            | Select (Expr t) String
            | Atom Atom
            deriving Show

data Type = TypeForAll [Unique] Type
          | TypeArrow Type Type
          | RecordType Row
          | TypeVar Unique
          | PrimType String
          deriving (Show, Eq)

type Row = [(String, Type)]

data Atom = Var String
          | Const Const
          deriving Show

data Const = ConstInt Int
           deriving Show
