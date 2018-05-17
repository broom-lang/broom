module Ast (Expr(..), Type(..), Atom(..), Const(..)) where

import Data.Unique (Unique, hashUnique)

import Primop (Primop)

instance Show Unique where
    show uq = "t" ++ show (hashUnique uq)

data Expr t = Data String [(String, Type)] (Expr t)
            | Lambda String t (Expr t)
            | App (Expr t) (Expr t)
            | PrimApp Primop (Expr t) (Expr t)
            | Let String t (Expr t) (Expr t)
            | LetRec String t (Expr t) (Expr t)
            | Case (Expr t) [(String, String, Expr t)]
            | If (Expr t) (Expr t) (Expr t)
            | Record [(String, Expr t)]
            | Select (Expr t) String
            | Atom Atom
            deriving Show

data Type = TypeForAll [Unique] Type
          | TypeArrow Type Type
          | RecordType Row
          | DataType Unique Row
          | TypeVar Unique
          | PrimType String
          deriving (Show, Eq)

type Row = [(String, Type)]

data Atom = Var String
          | Const Const
          deriving Show

data Const = ConstInt Int
           deriving Show
