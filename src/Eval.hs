{-# LANGUAGE TupleSections #-}

module Eval (eval, runEvaluation, emptyEnv) where

import qualified Data.HashMap.Lazy as Map
import Data.Maybe (fromJust) -- FIXME
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Foldable (traverse_)
import Control.Monad.Trans (liftIO)
import Control.Monad.Except (ExceptT, runExceptT, throwError)

import Ast (Expr(..), Decl(..), definiends, Atom(..), Const(..), Type)
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

newtype Env = Env (Map.HashMap String (IORef (Maybe Value)))

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
emptyEnv = Env Map.empty

envDeclare :: [String] -> Env -> IO Env
envDeclare names (Env bindings) = Env <$> (Map.union <$> newBindings <*> pure bindings)
    where newBindings = Map.fromList <$> traverse newBinding names
          newBinding name = (name,) <$> newIORef Nothing

envInit :: String -> Value -> Env -> IO ()
envInit name value (Env bindings) = writeIORef (fromJust (Map.lookup name bindings)) (Just value)

envDefine :: String -> Value -> Env -> IO Env
envDefine name value (Env bindings) = do var <- newIORef (Just value)
                                         return $ Env (Map.insert name var bindings)

envLookup :: String -> Env -> IO (Maybe Value)
envLookup name (Env bindings) =
    case Map.lookup name bindings of
        Just var -> readIORef var
        Nothing -> return Nothing

eval :: Env -> Expr Type -> Evaluation Value
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
eval env (Let decls body) = do env <- liftIO $ envDeclare (definiends =<< decls) env
                               traverse_ (exec env) decls
                               eval env body
eval env (Case matchee matches) =
    do matcheev <- eval env matchee
       case matcheev of
           Variant tag contents ->
               let evalMatch ((matchTag, param, body):_) | tag == matchTag =
                       do env' <- liftIO $ envDefine param contents env
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

exec :: Env -> Decl Type -> Evaluation ()
exec env (Val name _ expr) = do v <- eval env expr
                                liftIO $ envInit name v env
exec env (Data name variants) = liftIO $ traverse_ (initCtor env) variants
    where initCtor env (tag, _) = envInit tag (Constructor tag) env

apply :: Value -> Value -> Evaluation Value
apply (Closure param body env) arg =
    do env' <- liftIO $ envDefine param arg env
       eval env' body
apply (Constructor tag) arg = return $ Variant tag arg
apply f _ = throwError $ NonCallable f
