module Eval (eval, emptyEnv) where

import Data.Maybe (fromJust)

import Ast (Expr(..), Atom(..), Const(..))

newtype Env = Env [(String, Value)]
            deriving Show

data Value = Closure String Expr Env
           | Int Int
           deriving Show

emptyEnv :: Env
emptyEnv = Env []

eval :: Env -> Expr -> Value
eval env (Lambda param body) = Closure param body env
eval env (App f arg) = apply (eval env f) (eval env arg)
eval (Env env) (Atom (Var name)) = fromJust (lookup name env)
eval _ (Atom (Const (ConstInt n)))  = Int n

apply :: Value -> Value -> Value
apply (Closure param body (Env env)) arg = eval (Env ((param, arg) : env)) body
