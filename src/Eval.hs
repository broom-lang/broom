module Eval (eval, emptyEnv) where

import Data.Maybe (fromJust)
import Data.Bifunctor (second)
import Data.Foldable (foldl')

import Ast (Expr(..), Atom(..), Const(..), Type)
import Primop (Primop(..))

newtype Env = Env [(String, Value)]
            deriving Show

data Value = Closure String (Expr Type) Env
           | Struct [(String, Value)]
           | Constructor String
           | Variant String Value
           | Int Int
           | Bool Bool
           deriving Show

emptyEnv :: Env
emptyEnv = Env []

envInsert :: Env -> String -> Value -> Env
envInsert (Env bindings) name value = Env $ (name, value) : bindings

envLookup :: String -> Env -> Maybe Value
envLookup name (Env bindings) = lookup name bindings

eval :: Env -> Expr Type -> Value
eval env (Data _ variants body) =
    let env' = foldl' insertCtor env variants
    in  eval env' body
    where insertCtor env (tag, _) = envInsert env tag (Constructor tag)
eval env (Lambda param _ body) = Closure param body env
eval env (App f arg) = apply (eval env f) (eval env arg)
eval env (PrimApp op l r) = operate (eval env l) (eval env r)
    where operate = case op of
                        Eq  -> \(Int a) (Int b) -> Bool $ a == b
                        Add -> \(Int a) (Int b) -> Int $ a + b
                        Sub -> \(Int a) (Int b) -> Int $ a - b
                        Mul -> \(Int a) (Int b) -> Int $ a * b
                        Div -> \(Int a) (Int b) -> Int $ div a b
eval env (Let name _ expr body) =
    let env' = envInsert env name (eval env expr)
    in  eval env' body
eval env (Case matchee matches) =
    case eval env matchee of
        Variant tag contents ->
            let evalMatch ((matchTag, param, body):_) | tag == matchTag =
                    let env' = envInsert env param contents
                    in  eval env' body
                evalMatch (_:matches) = evalMatch matches
                evalMatch [] = error $ "No branch for tag " ++ tag
            in evalMatch matches
        _ -> error $ "Tried to match nonvariant " ++ show matchee
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
apply (Constructor tag) arg = Variant tag arg
apply _ arg = error $ "Noncallable: " ++ show arg
