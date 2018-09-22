module Typecheck (TypeError, typecheck) where

import Data.Maybe (fromJust)
import Data.List (foldl', nub, (\\))
import qualified Data.HashMap.Lazy as Map
import Control.Monad (foldM)
import Control.Unification ( BindingMonad(..), Fallible(..), UTerm(..), bindVar, unify, getFreeVars
                           , freshen, applyBindings, freeze )
import Control.Unification.IntVar (IntVar, IntBindingT, evalIntBindingT)
import Control.Monad.Trans (lift, liftIO)
import Control.Monad.Except (MonadError, ExceptT, runExceptT, throwError)
import Control.Monad.Reader (MonadReader, ReaderT, runReaderT, asks, local)

import Util (Name, nameFromIntVar, nameFromString)
import qualified Ast
import Ast (Expr(..), Atom(..), Const(..))
import Type (Type(..), MonoType(..), PrimType(..),
             OpenType, ClosedType, OpenMonoType, ClosedMonoType)

type Map = Map.HashMap

-- Utils for Control.Unification
-- =================================================================================================

applyExprBindings :: Expr OpenType -> Typing (Expr OpenType)
applyExprBindings =
    \case Lambda param (TypeForAll [] t) body ->
              Lambda param <$> (TypeForAll [] <$> Typing (lift (applyBindings t)))
                           <*> applyExprBindings body
          expr @ (Atom _) -> pure expr

freezeExpr :: Expr OpenType -> Expr ClosedType
freezeExpr =
    \case Lambda param (TypeForAll [] t) body ->
              Lambda param (TypeForAll [] $ fromJust $ freeze t) (freezeExpr body)
          Atom a -> Atom a

ctxFreeVars :: Ctx -> Typing [IntVar]
ctxFreeVars (Ctx kvs) = foldM step [] kvs
    where step frees (TypeForAll _ t) = (++ frees) <$> liftUnify (getFreeVars t)

-- Errors
-- =================================================================================================

data TypeError = Occurs IntVar OpenMonoType
               | TypeShapes (MonoType OpenMonoType) (MonoType OpenMonoType)
               | Rank2 Name Ast.Type
               | Unbound Name
               | UnboundType Name
               deriving Show

instance Fallible MonoType IntVar TypeError where
    occursFailure = Occurs
    mismatchFailure = TypeShapes

-- Contexts
-- =================================================================================================

newtype Env = Env (Map Name OpenMonoType)

builtinEnv :: Env
builtinEnv = Env $ Map.fromList $ [(nameFromString "Int", UTerm $ PrimType TypeInt)]

envLookup :: Name -> Env -> Maybe OpenMonoType
envLookup name (Env kvs) = Map.lookup name kvs

envPush :: [Name] -> [OpenMonoType] -> (Env, Ctx) -> (Env, Ctx)
envPush names types (Env kvs, ctx) = (Env $ foldl' step kvs (zip names types), ctx)
    where step kvs (k, v) = Map.insert k v kvs

newtype Ctx = Ctx (Map Name OpenType)

emptyCtx :: Ctx
emptyCtx = Ctx Map.empty

lookupType :: Name -> Ctx -> Typing OpenType
lookupType name (Ctx kvs) = case Map.lookup name kvs of
                                Just t -> pure t
                                Nothing -> throwError $ Unbound name

ctxPush :: Name -> OpenType -> (Env, Ctx) -> (Env, Ctx)
ctxPush name t (env, Ctx kvs) = (env, Ctx $ Map.insert name t kvs)

-- The Monad
-- =================================================================================================

newtype Typing a = Typing { unTyping :: ReaderT (Env, Ctx)
                                                (ExceptT TypeError (IntBindingT MonoType IO)) a }
                 deriving (Functor, Applicative, Monad)

deriving instance MonadReader (Env, Ctx) Typing

deriving instance MonadError TypeError Typing

runTyping :: Env -> Ctx -> Typing a -> IO (Either TypeError a)
runTyping env ctx = evalIntBindingT . runExceptT . flip runReaderT (env, ctx) . unTyping

liftUnify :: IntBindingT MonoType IO a -> Typing a
liftUnify = Typing . lift . lift

getEnv :: Typing Env
getEnv = asks fst

getCtx :: Typing Ctx
getCtx = asks snd

-- Type Checking Algorithms
-- =================================================================================================

hydrate :: Env -> Ast.Type -> Typing OpenType
hydrate env (Ast.TypeForAll params t) =
    -- Create OpaqueType:s bound at the TypeForAll for params, add them to the Env and monoHydrate t
    do params' <- liftUnify $ traverse (const $ nameFromIntVar <$> freeVar) params
       let paramRefs = fmap (UTerm . OpaqueType) params'
       local (envPush params paramRefs) (TypeForAll params' <$> monoHydrate t)
hydrate env (Ast.MonoType t) = TypeForAll [] <$> monoHydrate t

monoHydrate :: Ast.MonoType -> Typing OpenMonoType
monoHydrate =
    \case Ast.TypeArrow d cd -> UTerm <$> (TypeArrow <$> monoHydrate d <*> monoHydrate cd)
          Ast.RecordType row -> UTerm . RecordType <$> traverse hydrateEntry row
              where hydrateEntry (k, v) = (k,) <$> monoHydrate v
          Ast.TypeName name -> do ot <- envLookup name <$> getEnv
                                  case ot of
                                      Just t -> pure t
                                      Nothing -> throwError $ UnboundType name

generalize :: OpenMonoType -> Typing OpenType
generalize t = do frees <- liftUnify $ getFreeVars t
                  nonLocals <- ctxFreeVars =<< getCtx
                  let bindables = nub frees \\ nub nonLocals
                  flip TypeForAll t <$> traverse bind bindables
               where bind v = do let param = nameFromIntVar v
                                 liftUnify $ bindVar v (UTerm $ OpaqueType param)
                                 return param

instantiate :: OpenType -> Typing OpenMonoType
instantiate (TypeForAll params t) = Typing $ lift $ freshen t

typed :: Expr (Maybe Ast.Type) -> Typing (Expr OpenType, OpenMonoType)
typed =
    \case Lambda param srcT body ->
              do monoDomain <- case srcT of
                                   Just (Ast.MonoType t) -> monoHydrate t
                                   Just t @ (Ast.TypeForAll _ _) -> throwError $ Rank2 param t
                                   Nothing -> UVar <$> liftUnify freeVar
                 let domain = TypeForAll [] monoDomain
                 (body', codomain) <- local (ctxPush param domain) (typed body)
                 return (Lambda param domain body', UTerm $ TypeArrow monoDomain codomain)
          Atom v @ (Var name) -> (Atom v,) <$> (instantiate =<< lookupType name =<< getCtx)
          Atom c @ (Const (ConstInt _)) -> pure (Atom c, UTerm $ PrimType TypeInt)

-- Connecting the Wires
-- =================================================================================================

typecheck :: Expr (Maybe Ast.Type) -> IO (Either TypeError (Expr ClosedType, ClosedType))
typecheck expr = runTyping builtinEnv emptyCtx typing
    where typing = do (expr', t) <- typed expr
                      TypeForAll params t' <- generalize t
                      t'' <- fromJust . freeze <$> Typing (lift (applyBindings t'))
                      expr'' <- freezeExpr <$> applyExprBindings expr'
                      return (expr'', TypeForAll params t'')
