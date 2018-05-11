module Eval (eval, emptyEnv) where

import Data.Maybe (fromJust)
import Data.Bifunctor (second)

import Ast (Expr(..), Atom(..), Const(..), Type)

newtype Env = Env [(String, Value)]
            deriving Show

data Value = Closure String (Expr Type) Env
           | Struct [(String, Value)]
           | Int Int
           deriving Show

emptyEnv :: Env
emptyEnv = Env []

envInsert :: Env -> String -> Value -> Env
envInsert (Env bindings) name value = Env $ (name, value) : bindings

envLookup :: String -> Env -> Maybe Value
envLookup name (Env bindings) = lookup name bindings

eval :: Env -> Expr Type -> Value
eval env (Lambda param _ body) = Closure param body env
eval env (App f arg) = apply (eval env f) (eval env arg)
eval env (Let name _ expr body) =
    let env' = envInsert env name (eval env expr)
    in  eval env' body
eval env (Record fields) = Struct $ second (eval env) <$> fields
eval env (Select record label) =
    case eval env record of
        Struct fields -> fromJust $ lookup label fields
        _ -> error $ "Not a record: " ++ show record
eval env (Atom (Var name)) = fromJust (envLookup name env)
eval _ (Atom (Const (ConstInt n)))  = Int n

apply :: Value -> Value -> Value
apply (Closure param body env) arg =
    let env' = envInsert env param arg
    in  eval env' body
