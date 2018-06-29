{-# LANGUAGE TupleSections, LambdaCase #-}

module Eval (Evaluation, runEvaluation, emptyEnv, eval) where

import qualified Data.HashMap.Lazy as Map
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Foldable (foldlM)
import Control.Monad.Trans (liftIO)
import Control.Monad.Except (ExceptT, runExceptT, throwError)

import Util (Name)
import Ast (Expr(..), Decl(..), Atom(..), Const(..))
import Primop (Primop(..))
import Type (Type)

type Map = Map.HashMap

data EvalError = NonCallable Value
               | NonRecord Value
               | NonBoolean Value
               | NoSuchField Name Row
               | Unbound Name
               | Uninitialized Name
               deriving Show

type Evaluation = ExceptT EvalError IO

runEvaluation :: Evaluation a -> IO (Either EvalError a)
runEvaluation = runExceptT

newtype Env = Env (Map Name (IORef (Maybe Value)))

instance Show Env where
    show = const "#<env>"

emptyEnv :: Env
emptyEnv = Env Map.empty

lookupVar :: Name -> Env -> Evaluation Value
lookupVar name (Env env) = case Map.lookup name env of
                               Just r ->
                                   liftIO (readIORef r) >>=
                                       \case Just v -> pure v
                                             Nothing -> throwError $ Uninitialized name
                               Nothing -> throwError $ Unbound name

insert :: Name -> Value -> Env -> Evaluation Env
insert k v (Env bindings) = do v <- liftIO (newIORef (Just v))
                               return $ Env $ Map.insert k v bindings

data Value = Closure Name (Expr Type) Env
           | Struct [(Name, Value)]
           | Int Int
           | Bool Bool
           deriving Show

type Row = [(Name, Value)]

eval :: Env -> Expr Type -> Evaluation Value
eval env expr =
    case expr of
        Lambda param _ body -> pure $ Closure param body env
        App f arg -> do { f <- eval env f; arg <- eval env arg; apply f arg }
            where apply :: Value -> Value -> Evaluation Value
                  apply (Closure param body env) arg = flip eval body =<< insert param arg env
                  apply f _ = throwError $ NonCallable f
        PrimApp op l r -> primApply op <$> eval env l <*> eval env r
            where primApply op =
                      case op of
                          Eq  -> \(Int a) (Int b) -> Bool $ a == b
                          Add -> \(Int a) (Int b) -> Int $ a + b
                          Sub -> \(Int a) (Int b) -> Int $ a - b
                          Mul -> \(Int a) (Int b) -> Int $ a * b
                          Div -> \(Int a) (Int b) -> Int $ div a b
        Let decls body -> flip eval body =<< foldlM exec env decls
        If cond conseq alt -> eval env cond >>= \case Bool True -> eval env conseq
                                                      Bool False -> eval env alt
                                                      v -> throwError $ NonBoolean v
        Record fields -> Struct <$> traverse (\(l, v) -> (l,) <$> eval env v) fields
        Select record label -> eval env record >>= \case Struct fields -> structGet label fields
                                                         v -> throwError $ NonRecord v
            where structGet :: Name -> Row -> Evaluation Value
                  structGet label fields = case lookup label fields of
                                               Just v -> pure v
                                               Nothing -> throwError $ NoSuchField label fields
        Atom (Var name) -> lookupVar name env
        Atom (Const (ConstInt n)) -> pure $ Int n

exec :: Env -> Decl Type -> Evaluation Env
exec env (Val name _ expr) = flip (insert name) env =<< eval env expr
