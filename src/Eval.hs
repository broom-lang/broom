{-# LANGUAGE TupleSections #-}

module Eval (eval, runEvaluation, emptyEnv) where

import Data.Maybe (fromJust)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Bifunctor (second)
import Data.Foldable (foldl')
import Control.Monad (foldM)
import Control.Monad.Trans (liftIO)
import Control.Monad.Except (ExceptT, runExceptT, throwError)

import Ast (Expr(..), Atom(..), Const(..), Type)
import Primop (Primop(..))

data EvalError = Match String
               | NonVariant Value
               | NonBoolean Value
               | NonRecord Value
               | NonCallable Value
               deriving Show

type Evaluation a = ExceptT EvalError IO a

runEvaluation :: Evaluation a -> IO (Either EvalError a)
runEvaluation = runExceptT

newtype Env = Env [(String, IORef (Maybe Value))]

instance Show Env where
    show = const "#<env>"

data Value = Closure String (Expr Type) Env
           | Struct [(String, Value)]
           | Constructor String
           | Variant String Value
           | Int Int
           | Bool Bool
           deriving Show

emptyEnv :: Env
emptyEnv = Env []

envInsert :: Env -> String -> IORef (Maybe Value) -> Env
envInsert (Env bindings) name var = Env ((name, var) : bindings)

envDefine :: Env -> String -> Value -> IO Env
envDefine env name value = envInsert env name <$> newIORef (Just value)

envLookup :: String -> Env -> IO (Maybe Value)
envLookup name (Env bindings) =
    case lookup name bindings of
        Just var -> readIORef var
        Nothing -> return Nothing

eval :: Env -> Expr Type -> Evaluation Value
eval env (Data _ variants body) =
    do env' <- liftIO $ foldM insertCtor env variants
       eval env' body
    where insertCtor env (tag, _) = envDefine env tag (Constructor tag)
eval env (Lambda param _ body) = return $ Closure param body env
eval env (App f arg) = do f <- eval env f
                          arg <- eval env arg
                          apply f arg
eval env (PrimApp op l r) = operate <$> eval env l <*> eval env r
    where operate = case op of
                        Eq  -> \(Int a) (Int b) -> Bool $ a == b
                        Add -> \(Int a) (Int b) -> Int $ a + b
                        Sub -> \(Int a) (Int b) -> Int $ a - b
                        Mul -> \(Int a) (Int b) -> Int $ a * b
                        Div -> \(Int a) (Int b) -> Int $ div a b
eval env (Let name _ expr body) =
    do env' <- liftIO . envDefine env name =<< eval env expr
       eval env' body
eval env (LetRec name _ expr body) =
    do var <- liftIO $ newIORef Nothing
       let env' = envInsert env name var
       exprv <- eval env' expr
       liftIO $ writeIORef var (Just exprv)
       eval env' body
eval env (Case matchee matches) =
    do matcheev <- eval env matchee
       case matcheev of
           Variant tag contents ->
               let evalMatch ((matchTag, param, body):_) | tag == matchTag =
                       do env' <- liftIO $ envDefine env param contents
                          eval env' body
                   evalMatch (_:matches) = evalMatch matches
                   evalMatch [] = throwError $ Match tag
               in evalMatch matches
           _ -> throwError $ NonVariant matcheev
eval env (If cond conseq alt) =
    do condv <- eval env cond
       case condv of
           Bool True -> eval env conseq
           Bool False -> eval env alt
           v -> throwError $ NonBoolean v
eval env (Record fields) =
    Struct <$> traverse (\(l, v) -> (l,) <$> eval env v) fields
eval env (Select record label) =
    do struct <- eval env record
       case struct of
           Struct fields -> return $ fromJust (lookup label fields)
           _ -> throwError $ NonRecord struct
eval env (Atom (Var name)) = liftIO $ fromJust <$> envLookup name env
eval _ (Atom (Const (ConstInt n)))  = return $ Int n

apply :: Value -> Value -> Evaluation Value
apply (Closure param body env) arg =
    do env' <- liftIO $ envDefine env param arg
       eval env' body
apply (Constructor tag) arg = return $ Variant tag arg
apply f _ = throwError $ NonCallable f
