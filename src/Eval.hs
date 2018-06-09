{-# LANGUAGE TupleSections #-}

module Eval (eval, emptyEnv) where

import qualified Data.HashMap.Lazy as Map
import Data.Maybe (fromJust) -- FIXME
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Foldable (traverse_)

import Ast (Expr(..), Decl(..), definiends, Atom(..), Const(..), Type)
import Primop (Primop(..))

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

eval :: Env -> Expr Type -> IO Value
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
eval env (Let decls body) = do env <- envDeclare (definiends =<< decls) env
                               traverse_ (exec env) decls
                               eval env body
eval env (Case matchee matches) =
    do matcheev <- eval env matchee
       case matcheev of
           Variant tag contents ->
               let evalMatch ((matchTag, param, body):_) | tag == matchTag =
                       do env' <- envDefine param contents env
                          eval env' body
                   evalMatch (_:matches) = evalMatch matches
                   evalMatch [] = error $ "No branch for tag " ++ tag
               in evalMatch matches
           _ -> error $ "Tried to match nonvariant " ++ show matchee
eval env (If cond conseq alt) =
    do condv <- eval env cond
       case condv of
           Bool True -> eval env conseq
           Bool False -> eval env alt
           v -> error $ "Not a boolean: " ++ show v
eval env (Record fields) =
    Struct <$> traverse (\(l, v) -> (l,) <$> eval env v) fields
eval env (Select record label) =
    do struct <- eval env record
       case struct of
           Struct fields -> return $ fromJust (lookup label fields)
           _ -> error $ "Not a record: " ++ show record
eval env (Atom (Var name)) = fromJust <$> envLookup name env
eval _ (Atom (Const (ConstInt n)))  = return $ Int n

exec :: Env -> Decl Type -> IO ()
exec env (Val name _ expr) = do v <- eval env expr
                                envInit name v env
exec env (Data name variants) = traverse_ (initCtor env) variants
    where initCtor env (tag, _) = envInit tag (Constructor tag) env

apply :: Value -> Value -> IO Value
apply (Closure param body env) arg =
    do env' <- envDefine param arg env
       eval env' body
apply (Constructor tag) arg = return $ Variant tag arg
apply _ arg = error $ "Noncallable: " ++ show arg -- FIXME
