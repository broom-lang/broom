module Ast (Expr(..), Decl(..), definiends, Atom(..), Const(..),
            Type(..), MonoType(..), Row) where

import Primop (Primop)

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
            | Data String Row
            deriving Show

definiends :: Decl t -> [String]
definiends (Val name _ _) = pure name
definiends (Data _ variants) = fst <$> variants

data Atom = Var String
          | Const Const
          deriving Show

data Const = ConstInt Int
           deriving Show

data Type = TypeForAll [String] MonoType
          | MonoType MonoType
          deriving (Show, Eq)

data MonoType = TypeArrow MonoType MonoType
              | RecordType Row
              | TypeName String
              deriving (Show, Eq)

type Row = [(String, MonoType)]
