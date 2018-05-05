module Ast where

data Expr = Lambda String Expr
          | App Expr Expr
          | Atom Atom
          deriving Show

data Atom = Var String
          | Const Const
          deriving Show

data Const = ConstInt Int
           deriving Show
