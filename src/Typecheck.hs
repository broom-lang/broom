{-# LANGUAGE TupleSections #-}

module Typecheck (typecheck) where

import Data.Maybe (fromJust)
import Data.List (foldl')
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Unique (Unique, newUnique, hashUnique)
import Control.Monad.Trans (liftIO, lift)
import Control.Monad.State.Lazy (StateT, runStateT, evalStateT, mapStateT, get, modify)
import Control.Monad.Except (ExceptT, runExceptT, mapExceptT, throwError,
                             Except)
import Control.Monad.Identity (Identity(..))
import Data.Bifunctor (bimap, second)

import Ast (Expr(..), Type(..), Atom(..), Const(..))

newtype Ctx = Ctx [(String, Type)]

emptyCtx :: Ctx
emptyCtx = Ctx []

ctxInsert :: Ctx -> String -> Type -> Ctx
ctxInsert (Ctx bindings) name typ = Ctx $ (name, typ) : bindings

ctxLookup :: String -> Ctx -> Maybe Type
ctxLookup name (Ctx bindings) = lookup name bindings

type Substitution = HashMap Unique Type

data UnificationError = PolytypeUnification Type
                      | UnificationShapes Type Type
                      | Occurs Unique Type
                      deriving Show

type Unification a = StateT Substitution (Except UnificationError) a

runUnification :: Unification () -> Typing ()
runUnification uf = mapStateT toTypeError uf
    where toTypeError exn = mapExceptT toIO exn
          toIO (Identity res) = return (bimap UnificationError id res)

unify :: Type -> Type -> Unification ()
unify (t @ (TypeForAll _ _)) _ = throwError $ PolytypeUnification t
unify _ (t @ (TypeForAll _ _)) = throwError $ PolytypeUnification t
unify t1 t2 =
    do t1 <- walk t1
       t2 <- walk t2
       unifyWalked t1 t2
    where unifyWalked t1 t2 | t1 == t2 = return ()
          unifyWalked (TypeVar name1) t2 = unifyVar name1 t2
          unifyWalked t1 (TypeVar name2) = unifyVar name2 t1
          unifyWalked (TypeArrow d1 cd1) (TypeArrow d2 cd2) =
              unify d1 d2 >> unify cd1 cd2
          unifyWalked t1 t2 = throwError $ UnificationShapes t1 t2

unifyVar :: Unique -> Type -> Unification ()
unifyVar name t =
    do occursCheck name t
       modify (HashMap.insert name t)

walk :: Type -> Unification Type
walk (t @ (TypeVar name)) =
    do subst <- get
       case HashMap.lookup name subst of
           Just val -> walk val
           Nothing -> return t
walk t = return t

occursCheck :: Unique -> Type -> Unification ()
occursCheck name t =
    do t <- walk t
       case t of
           TypeForAll _ _ -> throwError $ PolytypeUnification t
           TypeArrow d cd -> occursCheck name d >> occursCheck name cd
           TypeVar name' | name' == name -> throwError $ Occurs name t
           TypeVar _ -> return ()
           PrimType _ -> return ()

data TypeError = MonotypeSpecialization Type
               | UnificationError UnificationError
               deriving Show

type Typing a = StateT Substitution (ExceptT TypeError IO) a

runTyping :: Typing (Expr Type, Type) -> IO (Either TypeError (Expr Type, Type))
runTyping ting =
    do res <- runExceptT (runStateT ting HashMap.empty)
       return $ case res of
           Right (typing, subst) ->
               Right $ second (quantifyFrees emptyCtx . applySubst subst) typing
           Left err -> Left err

freshType :: Typing Type
freshType = TypeVar <$> liftIO newUnique

quantifyFrees :: Ctx -> Type -> Type
quantifyFrees ctx t =
    case frees of
        _:_ -> TypeForAll frees t
        [] -> t
    where frees = HashSet.toList $ HashSet.difference (typeFrees t)
                                                      (ctxBounds ctx)

typeFrees :: Type -> HashSet Unique
typeFrees (TypeForAll params t) =
    HashSet.difference (typeFrees t) (HashSet.fromList params)
typeFrees (TypeArrow d cd) =
    HashSet.union (typeFrees d) (typeFrees cd)
typeFrees (TypeVar name) = HashSet.singleton name
typeFrees (PrimType _) = HashSet.empty

ctxBounds :: Ctx -> HashSet Unique
ctxBounds (Ctx ctx) =
    foldl' (\frees (_, t) -> HashSet.union (typeBounds t) frees)
           HashSet.empty ctx
    where typeBounds (TypeForAll params t) =
              HashSet.union (HashSet.fromList params) (typeBounds t)
          typeBounds (TypeArrow d cd) =
              HashSet.union (typeBounds d) (typeBounds cd)
          typeBounds (TypeVar _) = HashSet.empty
          typeBounds (PrimType _) = HashSet.empty

specialize :: Type -> ExceptT TypeError IO Type
specialize (TypeForAll params t) =
    do params' <- liftIO $ traverse (const newUnique) params
       return $ replace (HashMap.fromList (zip params params')) t
    where replace env (TypeForAll _ t) = replace env t
          replace env (TypeArrow d cd) =
              TypeArrow (replace env d) (replace env cd)
          replace env (TypeVar name) =
              TypeVar (maybe name id (HashMap.lookup name env))
          replace _ (t @ (PrimType _)) = t
specialize t = return t

applySubst :: Substitution -> Type -> Type
applySubst subst (TypeForAll params t) = TypeForAll params $ applySubst subst t
applySubst subst (TypeArrow d cd) =
    TypeArrow (applySubst subst d) (applySubst subst cd)
applySubst subst (t @ (TypeVar name)) =
    case HashMap.lookup name subst of
        Just t -> applySubst subst t
        Nothing -> t
applySubst _ (t @ (PrimType _)) = t

typed :: Ctx -> Expr () -> Typing (Expr Type, Type)
typed ctx (Lambda param () body) =
    do domain <- freshType
       let ctx' = ctxInsert ctx param domain
       (body', codomain) <- typed ctx' body
       return (Lambda param domain body', TypeArrow domain codomain)
typed ctx (App f arg) =
    do (f', calleeType) <- typed ctx f
       (arg', argType) <- typed ctx arg
       codomain <- freshType
       runUnification (unify calleeType (TypeArrow argType codomain))
       return (App f' arg', codomain)
typed ctx (Let name () expr body) =
    do (expr', exprType) <- typed ctx expr
       let ctx' = ctxInsert ctx name (quantifyFrees ctx exprType)
       (body', bodyType) <- typed ctx' body
       return (Let name exprType expr' body', bodyType)
typed ctx (Atom atom) =
    case atom of
        Var name -> (Atom $ Var name,) <$> lift (specialize (fromJust (ctxLookup name ctx)))
        Const (ConstInt n) -> return (Atom $ Const $ ConstInt n, PrimType "Int")

typecheck :: Expr () -> IO (Either TypeError (Expr Type, Type))
typecheck = runTyping . typed emptyCtx
