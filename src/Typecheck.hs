{-# LANGUAGE TupleSections, FlexibleContexts #-}

module Typecheck (typecheck) where

import Data.Maybe (fromJust)
import Data.List (foldl', find)
import qualified Data.HashMap.Lazy as Map
import qualified Data.HashSet as Set
import Data.Unique (Unique, newUnique)
import Control.Monad (foldM)
import Control.Monad.Trans (liftIO, lift)
import Control.Monad.State.Lazy (StateT, runStateT, mapStateT)
import Control.Monad.Except (ExceptT, runExceptT, mapExceptT, throwError, Except)
import Control.Monad.Identity (Identity(..))
import Data.Bifunctor (bimap, first, second)

import Ast (Expr(..), Decl(..), Type(..), Atom(..), Const(..))
import qualified Primop
import Unify (Substitution, Unification, UnificationError, unify)

type Map = Map.HashMap
type Set = Set.HashSet

-- Context

newtype Ctx = Ctx (Map String Type)

emptyCtx :: Ctx
emptyCtx = Ctx Map.empty

ctxInsert :: Ctx -> String -> Type -> Ctx
ctxInsert (Ctx bindings) name typ = Ctx $ Map.insert name typ bindings

ctxLookup :: String -> Ctx -> Maybe Type
ctxLookup name (Ctx bindings) = Map.lookup name bindings

-- Type checking utils

data TypeError = MonotypeSpecialization Type
               | UnificationError UnificationError
               | InexistentField String Type
               | NonRecord Type
               | NonSum Type
               | CaseTags (Set String) (Set String)
               deriving Show

type Typing a = StateT Substitution (ExceptT TypeError IO) a

runTyping :: Typing (Expr Type, Type) -> IO (Either TypeError (Expr Type, Type))
runTyping ting =
    do res <- runExceptT (runStateT ting Map.empty)
       return $ case res of
           Right (typing, subst) ->
               Right $ bimap (exprSubst subst)
                             (quantifyFrees emptyCtx . applySubst subst)
                             typing
           Left err -> Left err



liftUnify :: Unification a -> Typing a
liftUnify uf = mapStateT toTypeError uf
    where toTypeError exn = mapExceptT toIO exn
          toIO (Identity res) = return (bimap UnificationError id res)

freshType :: Typing Type
freshType = TypeVar <$> liftIO newUnique

quantifyFrees :: Ctx -> Type -> Type
quantifyFrees ctx t =
    case frees of
        _:_ -> TypeForAll frees t
        [] -> t
    where frees = Set.toList $ Set.difference (typeFrees t) (ctxFrees ctx)

typeFrees :: Type -> Set Unique
typeFrees (TypeForAll params t) =
    Set.difference (typeFrees t) (Set.fromList params)
typeFrees (TypeArrow d cd) =
    Set.union (typeFrees d) (typeFrees cd)
typeFrees (RecordType row) = rowFrees row
typeFrees (DataType _ row) = rowFrees row
typeFrees (TypeVar name) = Set.singleton name
typeFrees (PrimType _) = Set.empty

rowFrees :: [(String, Type)] -> Set Unique
rowFrees = foldl' (\frees (_, t) -> Set.union frees (typeFrees t)) Set.empty

ctxFrees :: Ctx -> Set Unique
ctxFrees (Ctx ctx) =
    Map.foldl' (\frees t -> Set.union (typeFrees t) frees) Set.empty ctx

specialize :: Type -> ExceptT TypeError IO Type
specialize (TypeForAll params t) =
    do params' <- liftIO $ traverse (const newUnique) params
       return $ replace (Map.fromList (zip params params')) t
    where replace env (TypeForAll _ t) = replace env t
          replace env (TypeArrow d cd) =
              TypeArrow (replace env d) (replace env cd)
          replace env (DataType i row) = DataType i (replaceRow env row)
          replace env (RecordType row) = RecordType (replaceRow env row)
          replace env (TypeVar name) =
              TypeVar (maybe name id (Map.lookup name env))
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
    case Map.lookup name subst of
        Just t -> applySubst subst t
        Nothing -> t
applySubst _ (t @ (PrimType _)) = t

exprSubst :: Substitution -> Expr Type -> Expr Type
exprSubst subst (Lambda param t body) = Lambda param (applySubst subst t) (exprSubst subst body)
exprSubst subst (App f arg) = App (exprSubst subst f) (exprSubst subst arg)
exprSubst subst (PrimApp op l r) = PrimApp op (exprSubst subst l) (exprSubst subst r)
exprSubst subst (Let decls body) = Let (map (declSubst subst) decls) (exprSubst subst body)
exprSubst subst (Case matchee cases) =
    Case (exprSubst subst matchee) (map (second (exprSubst subst)) cases)
exprSubst subst (If cond conseq alt) =
    If (exprSubst subst cond) (exprSubst subst conseq) (exprSubst subst alt)
exprSubst subst (Record fields) = Record (map (second (exprSubst subst)) fields)
exprSubst subst (Select record label) = Select (exprSubst subst record) label
exprSubst _ (Atom atom) = Atom $ case atom of
                                     Var name -> Var name
                                     Const c -> Const c

declSubst :: Substitution -> Decl Type -> Decl Type
declSubst subst (Val name t expr) = Val name (applySubst subst t) (exprSubst subst expr)
declSubst subst (Data name variants) = Data name (map (second (applySubst subst)) variants)

-- The actual type checking

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
       liftUnify (unify calleeType (TypeArrow argType codomain))
       return (App f' arg', codomain)
typed ctx (PrimApp op l r) =
    do (l', lType) <- typed ctx l
       (r', rType) <- typed ctx r
       liftUnify (unify lType (PrimType "Int"))
       liftUnify (unify rType (PrimType "Int"))
       let t = case op of
                   Primop.Eq -> PrimType "Bool"
                   _ -> PrimType "Int"
       return (PrimApp op l' r', t)
typed (Ctx ctx) (Let decls body) =
    do Ctx ctxExtension <- liftIO $ declsCtx decls
       let ctx' = Ctx $ Map.union ctxExtension ctx
       decls' <- traverse (typedDecl ctx') decls
       let ctx'' = Ctx $ Map.union (quantifyFrees (Ctx ctx) <$> ctxExtension) ctx
       (body', bodyType) <- typed ctx'' body
       return (Let decls' body', bodyType)
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
typed ctx (If cond conseq alt) =
    do (cond', condType) <- typed ctx cond
       liftUnify (unify condType (PrimType "Bool"))
       (conseq', conseqType) <- typed ctx conseq
       (alt', altType) <- typed ctx alt
       liftUnify (unify conseqType altType)
       return (If cond' conseq' alt', conseqType)
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

typedDecl :: Ctx -> Decl () -> Typing (Decl Type)
typedDecl ctx (Val name _ expr) = do (expr', exprType) <- typed ctx expr
                                     return $ Val name (quantifyFrees ctx exprType) expr'
typedDecl ctx (Data name variants) = pure $ Data name variants

declsCtx :: [Decl ()] -> IO Ctx
declsCtx decls = Ctx . (\ctx -> foldl' (flip Map.union) Map.empty ctx) <$> traverse declCtx decls
    where declCtx (Val name _  _) = Map.singleton name . TypeVar <$> newUnique
          declCtx (Data name variants) =
              do dataType <- DataType <$> newUnique <*> pure variants
                 return $ foldl' (insertCtorType dataType) (Map.singleton name dataType) variants
              where insertCtorType dataType ctx (tag, domain) =
                        Map.insert tag (TypeArrow domain dataType) ctx

-- typed ctx (LetRec name () expr body) =
--     do exprType <- freshType
--        (expr', exprType') <- typed (ctxInsert ctx name exprType) expr
--        let ctx' = ctxInsert ctx name (quantifyFrees ctx exprType')
--        (body', bodyType) <- typed ctx' body
--        return (LetRec name exprType expr' body', bodyType)
-- typed ctx (Data name variants body) =
--     do dataType <- DataType <$> liftIO newUnique <*> pure variants
--        let ctx' = foldl' (insertCtorType dataType) (ctxInsert ctx name dataType) variants
--        first (Data name variants) <$> typed ctx' body
--     where insertCtorType dataType ctx (tag, domain) = ctxInsert ctx tag (TypeArrow domain dataType)

typecheck :: Expr () -> IO (Either TypeError (Expr Type, Type))
typecheck = runTyping . typed emptyCtx
