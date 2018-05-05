module Ast where

data Expr = Lambda String Type Expr
          | App Expr Expr
          | Atom Atom
          deriving Show

data Type = TypeArrow Type Type
          | PrimType String
          deriving (Eq, Show)

data Atom = Var String
          | Const Const
          deriving Show

data Const = ConstInt Int
           deriving Show
