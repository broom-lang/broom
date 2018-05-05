module Ast where

data Expr = Const Const
          deriving Show

data Const = Int Int
           deriving Show
