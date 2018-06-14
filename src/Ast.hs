module Ast (Expr(..), Decl(..), definiends, Atom(..), Const(..),
            Type(..), MonoType(..), Row) where

import Util (Name)
import Primop (Primop)

data Expr t = Lambda Name t (Expr t)
            | App (Expr t) (Expr t)
            | PrimApp Primop (Expr t) (Expr t)
            | Let [Decl t] (Expr t)
            | Case (Expr t) [(Name, Name, Expr t)]
            | If (Expr t) (Expr t) (Expr t)
            | Record [(Name, Expr t)]
            | Select (Expr t) Name
            | Atom Atom
            deriving Show

data Decl t = Val Name t (Expr t)
            | Data Name Row
            deriving Show

definiends :: Decl t -> [Name]
definiends (Val name _ _) = pure name
definiends (Data _ variants) = fst <$> variants

data Atom = Var Name
          | Const Const
          deriving Show

data Const = ConstInt Int
           deriving Show

data Type = TypeForAll [Name] MonoType
          | MonoType MonoType
          deriving (Show, Eq)

data MonoType = TypeArrow MonoType MonoType
              | RecordType Row
              | TypeName Name
              deriving (Show, Eq)

type Row = [(Name, MonoType)]
