module Ast (Expr(..), Decl(..), definiends, Type(..), Atom(..), Const(..)) where

import Data.Unique (Unique, hashUnique)

import Primop (Primop)

instance Show Unique where
    show uq = "t" ++ show (hashUnique uq)

data Expr t = Lambda String t (Expr t)
            | App (Expr t) (Expr t)
            | PrimApp Primop (Expr t) (Expr t)
            | Let [Decl t] (Expr t)
            | Case (Expr t) [(String, String, Expr t)]
            | If (Expr t) (Expr t) (Expr t)
            | Record [(String, Expr t)]
            | Select (Expr t) String
            | Atom Atom
            deriving Show

data Decl t = Val String t (Expr t)
            | Data String [(String, Type)]
            deriving Show

definiends :: Decl t -> [String]
definiends (Val name _ _) = pure name
definiends (Data _ variants) = fst <$> variants

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
