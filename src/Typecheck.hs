{-# LANGUAGE TupleSections #-}

module Typecheck (TypeError, Typing, typecheck) where

import Data.Maybe (isJust)
import Data.List (foldl', find, nub, (\\))
import qualified Data.HashMap.Lazy as Map
import qualified Data.HashSet as Set
import Data.Bifunctor (first, second)
import Control.Monad (foldM)
import Control.Monad.Trans (lift, liftIO)
import Control.Monad.Except (ExceptT, runExceptT, withExceptT, throwError)
import Control.Monad.Reader (ReaderT, runReaderT, ask, local)

import Util (Name, nameFromString, freshName)
import qualified Ast
import Ast (Expr(..), Decl(..), Atom(..), Const(..))
import Primop (Primop(..))
import Type (Kind(..), Type(..), MonoType(..), TypeVar, newTypeVar, readTypeVar, writeTypeVar, Row)
import Unify (UnificationError, Unification, runUnify, unify)

type Set = Set.HashSet

type Ctx = Map.HashMap Name Type

type TypeCtx = Map.HashMap Name Kind

data TypeError = Rank2 Name Ast.Type
               | UnificationError UnificationError
               | InexistentField Name MonoType
               | NonArrow Type
               | NonRecord MonoType
               | Unbound Name
               | UnboundType Name
               deriving Show

type Typing a = ExceptT TypeError (ReaderT TypeCtx IO) a

getTypeCtx :: Typing TypeCtx
getTypeCtx = lift ask

liftUnify :: Unification a -> Typing a
liftUnify unification =
    do ures <- liftIO $ runUnify unification
       case ures of
           Left err -> throwError $ UnificationError err
           Right v -> pure v

freshType :: Typing MonoType
freshType = liftIO $ TypeVar <$> newTypeVar

lookupType :: Name -> Ctx -> Typing Type
lookupType name ctx =
    case Map.lookup name ctx of
        Just t -> pure t
        Nothing -> throwError $ Unbound name

pushKinds :: TypeCtx -> [Name] -> TypeCtx
pushKinds = foldl' (\kinder name -> Map.insert name Type kinder)

typeFrees :: Type -> IO [TypeVar]
typeFrees (TypeForAll _ t) = monoTypeFrees t
typeFrees (MonoType t) = monoTypeFrees t

monoTypeFrees :: MonoType -> IO [TypeVar]
monoTypeFrees (TypeArrow d cd) = mappend <$> monoTypeFrees d <*> monoTypeFrees cd
monoTypeFrees (RecordType row) = rowFrees row
monoTypeFrees (DataType _ row) = rowFrees row
monoTypeFrees (TypeName _) = pure []
monoTypeFrees (TypeVar r) = maybe [r] (const []) <$> readTypeVar r
monoTypeFrees (PrimType _) = pure []

rowFrees :: Row -> IO [TypeVar]
rowFrees = foldMap (monoTypeFrees . snd)

ctxFrees :: Ctx -> IO [TypeVar]
ctxFrees = foldMap typeFrees

generalize :: Ctx -> MonoType -> IO Type
generalize ctx t =
    do frees <- (\\) <$> (nub <$> monoTypeFrees t) <*> (nub <$> ctxFrees ctx)
       case frees of
           frees @ (_ : _) -> flip TypeForAll t <$> traverse bind frees
               where bind r = do name <- freshName "t"
                                 writeTypeVar r (TypeName name)
                                 return name
           [] -> pure $ MonoType t

substitute :: Map.HashMap Name MonoType -> MonoType -> IO MonoType
substitute subst (TypeArrow t u) = TypeArrow <$> substitute subst t <*> substitute subst u
substitute subst (RecordType row) = RecordType <$> substituteRow subst row
substitute subst (DataType name row) = DataType name <$> substituteRow subst row
substitute subst t @ (TypeName name) = pure $ maybe t id (Map.lookup name subst)
substitute subst t @ (TypeVar r) =
    do ot <- readTypeVar r
       case ot of
           Just t -> substitute subst t
           Nothing -> pure t
substitute _ t @ (PrimType _) = pure t

substituteRow :: Map.HashMap Name MonoType -> Row -> IO Row
substituteRow subst row = traverse (\(label, t) -> (label,) <$> substitute subst t) row

instantiate :: Type -> Typing MonoType
instantiate (MonoType t) = pure t
instantiate (TypeForAll params t) =
    do params' <- traverse (const freshType) params
       liftIO $ substitute (Map.fromList (zip params params')) t

hydrate :: TypeCtx -> Ast.Type -> Typing Type
hydrate kinder (Ast.TypeForAll params t) =
    TypeForAll params <$> monoHydrate (pushKinds kinder params) t
hydrate kinder (Ast.MonoType t) = MonoType <$> monoHydrate kinder t

monoHydrate :: TypeCtx -> Ast.MonoType -> Typing MonoType
monoHydrate kinder (Ast.TypeArrow domain codomain) =
    TypeArrow <$> monoHydrate kinder domain <*> monoHydrate kinder codomain
monoHydrate kinder (Ast.RecordType row) = RecordType <$> traverse hydrateEntry row
    where hydrateEntry (k, v) = (k,) <$> monoHydrate kinder v
monoHydrate kinder (Ast.TypeName name) =
    case show name of
        _ | isJust (Map.lookup name kinder) -> pure $ TypeName name
        "Int" -> pure $ PrimType $ nameFromString "Int"
        "Bool" -> pure $ PrimType $ nameFromString "Bool"
        _ -> throwError $ UnboundType name

typed :: Ctx -> Expr (Maybe Ast.Type) -> Typing (Expr Type, MonoType)
typed ctx (Lambda param synDomain body) =
    do kinder <- getTypeCtx
       monoDomain <- case synDomain of
                         Just (Ast.MonoType t) -> monoHydrate kinder t
                         Just t @ (Ast.TypeForAll _ _) -> throwError $ Rank2 param t
                         Nothing -> freshType
       let domain = MonoType monoDomain
       let ctx' = Map.insert param domain ctx
       (body', codomain) <- typed ctx' body
       return (Lambda param domain body', TypeArrow monoDomain codomain)
typed ctx (App f arg) =
    do (f', calleeType) <- typed ctx f
       (arg', domain) <- typed ctx arg
       codomain <- freshType
       liftUnify (unify calleeType (TypeArrow domain codomain))
       return (App f' arg', codomain)
typed ctx (PrimApp op l r) =
    do (l', lType) <- typed ctx l
       (r', rType) <- typed ctx r
       liftUnify (unify lType (PrimType (nameFromString "Int")))
       liftUnify (unify rType (PrimType (nameFromString "Int")))
       let t = case op of
                   Primop.Eq -> PrimType (nameFromString "Bool")
                   _ -> PrimType (nameFromString "Int")
       return (PrimApp op l' r', t)
typed ctx (Let decls body) =
    do (decls', ctx') <- foldM declStep ([], ctx) decls
       (body', bodyType) <- typed ctx' body
       return (Let (reverse decls') body', bodyType)
    where declStep (decls', ctx) decl = first (: decls') <$> typedDecl ctx decl
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
              do ctorType <- lookupType ctor ctx
                 case ctorType of
                     MonoType (TypeArrow paramType sumType) ->
                         let ctx' = Map.insert param (MonoType paramType) ctx
                         in do (body', resultType) <- typed ctx' body
                               return ((ctor, param, body'), sumType, resultType)
                     _ -> throwError $ NonArrow ctorType
typed ctx (If cond conseq alt) =
    do (cond', condType) <- typed ctx cond
       liftUnify (unify condType (PrimType (nameFromString "Bool")))
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
           RecordType row ->
               case find ((== label) . fst) row of
                   Just (_, fieldType) -> return (Select record' label, fieldType)
                   Nothing -> throwError $ InexistentField label recType
           _ -> throwError $ NonRecord recType
typed ctx (Atom (Var name)) =
    do t <- instantiate =<< lookupType name ctx
       return (Atom (Var name), t)
typed _ e @ (Atom (Const (ConstInt n))) =
    pure (Atom $ Const $ ConstInt n, PrimType $ nameFromString "Int")

typedDecl :: Ctx -> Decl (Maybe Ast.Type) -> Typing (Decl Type, Ctx)
typedDecl ctx (Val name synT expr) =
    do kinder <- getTypeCtx
       srcType <- traverse (hydrate kinder) synT
       local (maybePushKinds srcType) (k srcType)
    where maybePushKinds (Just (TypeForAll params _)) kinder = pushKinds kinder params
          maybePushKinds _ kinder = kinder
          k srcType =
              do (expr', exprMonoType) <- typed ctx expr
                 exprType <- liftIO $ generalize ctx exprMonoType
                 finalType <- case srcType of
                                  Just srcType -> do
                                      srcMonoType <- instantiate srcType
                                      -- FIXME: `val f: forall a . a = fn x => x` passes :(
                                      --   FIX: use unidirectional unification that can only alter
                                      --        `exprMonoType`
                                      liftUnify $ unify exprMonoType srcMonoType
                                      return srcType
                                  Nothing -> pure exprType
                 return (Val name finalType expr', Map.insert name finalType ctx)

resolve :: Expr Type -> IO (Expr Type)
resolve (Lambda name t body) = Lambda name <$> resolveType t <*> resolve body
resolve (App f arg) = App <$> resolve f <*> resolve arg
resolve (PrimApp op l r) = PrimApp op <$> resolve l <*> resolve r
resolve (Let decls body) = Let <$> traverse resolveDecl decls <*> resolve body
resolve (Case matchee cases) = Case <$> resolve matchee <*> traverse resolveCase cases
    where resolveCase (label, var, body) = (label, var,) <$> resolve body
resolve (If cond conseq alt) = If <$> resolve cond <*> resolve conseq <*> resolve alt
resolve (Record row) = Record <$> traverse (\(k, v) -> (k,) <$> resolve v) row
resolve (Select record label) = flip Select label <$> resolve record
resolve expr @ (Atom _) = pure expr

resolveDecl :: Decl Type -> IO (Decl Type)
resolveDecl (Val name t expr) = Val name <$> resolveType t <*> resolve expr

resolveType :: Type -> IO Type
resolveType (MonoType t) = MonoType <$> resolveMonoType t
resolveType t = pure t

resolveMonoType :: MonoType -> IO (MonoType)
resolveMonoType t @ (TypeVar r) = maybe t id <$> readTypeVar r
resolveMonoType t = pure t

typecheck :: Expr (Maybe Ast.Type) -> IO (Either TypeError (Expr Type, Type))
typecheck expr =
    let kinder = Map.empty
        ctx = Map.empty
        typing = do (expr, monoT) <- typed ctx expr
                    t <- liftIO $ generalize ctx monoT
                    liftIO $ (,) <$> resolve expr <*> resolveType t
    in  runReaderT (runExceptT typing) kinder
