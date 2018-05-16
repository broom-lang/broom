{-# LANGUAGE TupleSections, FlexibleContexts #-}

module Typecheck (typecheck) where

import Data.Maybe (fromJust)
import Data.List (foldl', find)
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Unique (Unique, newUnique)
import Data.Foldable (traverse_)
import Control.Monad (foldM)
import Control.Monad.Trans (liftIO, lift)
import Control.Monad.State.Lazy (StateT, runStateT, mapStateT, get, modify)
import Control.Monad.Except (ExceptT, runExceptT, mapExceptT, throwError,
                             Except)
import Control.Monad.Identity (Identity(..))
import Data.Bifunctor (bimap, first, second)

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

liftUnify :: Unification a -> Typing a
liftUnify uf = mapStateT toTypeError uf
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
           RecordType row -> checkRow row
           DataType _ row -> checkRow row
           TypeVar name' | name' == name -> throwError $ Occurs name t
           TypeVar _ -> return ()
           PrimType _ -> return ()
    where checkRow = traverse_ (occursCheck name . snd)

data TypeError = MonotypeSpecialization Type
               | UnificationError UnificationError
               | InexistentField String Type
               | NonRecord Type
               | NonSum Type
               | CaseTags (HashSet String) (HashSet String)
               deriving Show

type Typing a = StateT Substitution (ExceptT TypeError IO) a

runTyping :: Typing (Expr Type, Type) -> IO (Either TypeError (Expr Type, Type))
runTyping ting =
    do res <- runExceptT (runStateT ting HashMap.empty)
       return $ case res of
           Right (typing, subst) ->
               Right $ bimap (exprSubst subst)
                             (quantifyFrees emptyCtx . applySubst subst)
                             typing
           Left err -> Left err

freshType :: Typing Type
freshType = TypeVar <$> liftIO newUnique

quantifyFrees :: Ctx -> Type -> Type
quantifyFrees ctx t =
    case frees of
        _:_ -> TypeForAll frees t
        [] -> t
    where frees = HashSet.toList $ HashSet.difference (typeFrees t) (ctxFrees ctx)

typeFrees :: Type -> HashSet Unique
typeFrees (TypeForAll params t) =
    HashSet.difference (typeFrees t) (HashSet.fromList params)
typeFrees (TypeArrow d cd) =
    HashSet.union (typeFrees d) (typeFrees cd)
typeFrees (RecordType row) = rowFrees row
typeFrees (DataType _ row) = rowFrees row
typeFrees (TypeVar name) = HashSet.singleton name
typeFrees (PrimType _) = HashSet.empty

rowFrees :: [(String, Type)] -> HashSet Unique
rowFrees = foldl' (\frees (_, t) -> HashSet.union frees (typeFrees t)) HashSet.empty

ctxFrees :: Ctx -> HashSet Unique
ctxFrees (Ctx ctx) =
    foldl' (\frees (_, t) -> HashSet.union (typeFrees t) frees) HashSet.empty ctx

specialize :: Type -> ExceptT TypeError IO Type
specialize (TypeForAll params t) =
    do params' <- liftIO $ traverse (const newUnique) params
       return $ replace (HashMap.fromList (zip params params')) t
    where replace env (TypeForAll _ t) = replace env t
          replace env (TypeArrow d cd) =
              TypeArrow (replace env d) (replace env cd)
          replace env (DataType i row) = DataType i (replaceRow env row)
          replace env (RecordType row) = RecordType (replaceRow env row)
          replace env (TypeVar name) =
              TypeVar (maybe name id (HashMap.lookup name env))
          replace _ (t @ (PrimType _)) = t
          replaceRow env = map (second (replace env))
specialize t = return t

applySubst :: Substitution -> Type -> Type
applySubst subst (TypeForAll params t) = TypeForAll params $ applySubst subst t
applySubst subst (TypeArrow d cd) =
    TypeArrow (applySubst subst d) (applySubst subst cd)
applySubst subst (RecordType row) = RecordType $ second (applySubst subst) <$> row
applySubst subst (DataType i row) = DataType i $ second (applySubst subst) <$> row
applySubst subst (t @ (TypeVar name)) =
    case HashMap.lookup name subst of
        Just t -> applySubst subst t
        Nothing -> t
applySubst _ (t @ (PrimType _)) = t

exprSubst :: Substitution -> Expr Type -> Expr Type
exprSubst subst (Data name variants body) =
    Data name (map (second (applySubst subst)) variants) (exprSubst subst body)
exprSubst subst (Lambda param t body) = Lambda param (applySubst subst t) (exprSubst subst body)
exprSubst subst (App f arg) = App (exprSubst subst f) (exprSubst subst arg)
exprSubst subst (PrimApp op l r) = PrimApp op (exprSubst subst l) (exprSubst subst r)
exprSubst subst (Let name t expr body) =
    Let name (applySubst subst t) (exprSubst subst expr) (exprSubst subst body)
exprSubst subst (Case matchee cases) =
    Case (exprSubst subst matchee) (map (second (exprSubst subst)) cases)
exprSubst subst (Record fields) = Record (map (second (exprSubst subst)) fields)
exprSubst subst (Select record label) = Select (exprSubst subst record) label
exprSubst _ (Atom atom) = Atom $ case atom of
                                     Var name -> Var name
                                     Const c -> Const c

typed :: Ctx -> Expr () -> Typing (Expr Type, Type)
typed ctx (Data name variants body) =
    do dataType <- DataType <$> liftIO newUnique <*> pure variants
       let ctx' = foldl' (insertCtorType dataType) (ctxInsert ctx name dataType) variants
       first (Data name variants) <$> typed ctx' body
    where insertCtorType dataType ctx (tag, domain) = ctxInsert ctx tag (TypeArrow domain dataType)
typed ctx (Lambda param () body) =
    do domain <- freshType
       let ctx' = ctxInsert ctx param domain
       (body', codomain) <- typed ctx' body
       return (Lambda param domain body', TypeArrow domain codomain)
typed ctx (App f arg) =
    do (f', calleeType) <- typed ctx f
       (arg', argType) <- typed ctx arg
       codomain <- freshType
       liftUnify (unify calleeType (TypeArrow argType codomain))
       return (App f' arg', codomain)
typed ctx (PrimApp op l r) =
    do (l', lType) <- typed ctx l
       (r', rType) <- typed ctx r
       liftUnify (unify lType (PrimType "Int"))
       liftUnify (unify rType (PrimType "Int"))
       return (PrimApp op l' r', PrimType "Int")
typed ctx (Let name () expr body) =
    do (expr', exprType) <- typed ctx expr
       let ctx' = ctxInsert ctx name (quantifyFrees ctx exprType)
       (body', bodyType) <- typed ctx' body
       return (Let name exprType expr' body', bodyType)
typed ctx (Case matchee cases) =
    do (matchee', matcheeType) <- typed ctx matchee
       (cases', sumType, resultType) <- typedCases cases
       liftUnify (unify matcheeType sumType)
       return (Case matchee' (reverse cases'), resultType)
    where typedCases (match:matches) =
              do (match', sumType, resultType) <- typeCase match
                 foldM (\(matches', sumType, resultType) match ->
                            do (match', sumType', resultType') <- typeCase match
                               liftUnify (unify sumType sumType')
                               liftUnify (unify resultType resultType')
                               return (match':matches', sumType', resultType'))
                       ([match'], sumType, resultType) matches
          typedCases [] = error "unreachable"
          typeCase (ctor, param, body) =
              let TypeArrow paramType sumType = fromJust $ ctxLookup ctor ctx
                  ctx' = ctxInsert ctx param paramType
              in  do (body', resultType) <- typed ctx' body
                     return ((ctor, param, body'), sumType, resultType)
typed ctx (Record fields) =
    do (fields', row) <- unzip <$> traverse typedField fields
       return (Record fields', RecordType row)
    where typedField (name, expr) = do (expr', exprType) <- typed ctx expr
                                       return ((name, expr'), (name, exprType))
typed ctx (Select record label) =
    do (record', recType) <- typed ctx record
       case recType of
           RecordType row -> case find ((== label) . fst) row of
                                 Just (_, fieldType) -> return (Select record' label, fieldType)
                                 Nothing -> throwError $ InexistentField label recType
           _ -> throwError $ NonRecord recType
typed ctx (Atom atom) =
    case atom of
        Var name -> (Atom $ Var name,) <$> lift (specialize (fromJust (ctxLookup name ctx)))
        Const (ConstInt n) -> return (Atom $ Const $ ConstInt n, PrimType "Int")

typecheck :: Expr () -> IO (Either TypeError (Expr Type, Type))
typecheck = runTyping . typed emptyCtx
