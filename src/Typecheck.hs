module Typecheck (TypeError, Typing, typecheck) where

import qualified Data.HashMap.Lazy as Map
import Data.Bifunctor (second)
import Control.Monad.Trans (liftIO)
import Control.Monad.Except (ExceptT, runExceptT, withExceptT, throwError)

import Util (Name, nameFromString)
import Ast (Expr(..), Atom(..), Const(..))
import Type (Type(..), MonoType(..), TypeVar, newTypeVar)
import Unify (UnificationError, Unification, unify)

type Ctx = Map.HashMap Name Type

data TypeError = UnificationError UnificationError
               | Unbound Name
               deriving Show

type Typing a = ExceptT TypeError IO a

liftUnify :: Unification a -> Typing a
liftUnify = withExceptT UnificationError

freshType :: Typing MonoType
freshType = liftIO $ TypeVar <$> newTypeVar

lookupType :: Name -> Ctx -> Typing Type
lookupType name ctx =
    case Map.lookup name ctx of
        Just t -> pure t
        Nothing -> throwError $ Unbound name

substitute :: Map.HashMap Name MonoType -> MonoType -> MonoType
substitute subst (TypeArrow t u) = TypeArrow (substitute subst t) (substitute subst u)
substitute subst (RecordType row) = RecordType (second (substitute subst) <$> row)
substitute subst (DataType name row) = DataType name (second (substitute subst) <$> row)
substitute subst t @ (TypeName name) = maybe t id (Map.lookup name subst)
substitute _ t @ (TypeVar _) = t
substitute _ t @ (PrimType _) = t

instantiate :: Type -> Typing MonoType
instantiate (MonoType t) = pure t
instantiate (TypeForAll params t) =
    do params' <- traverse (const freshType) params
       return $ substitute (Map.fromList (zip params params')) t

typed :: Ctx -> Expr () -> Typing (Expr Type, MonoType)
typed ctx (Lambda param _ body) =
    do monoDomain <- freshType
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
typed ctx (Atom (Var name)) =
    do t <- instantiate =<< lookupType name ctx
       return (Atom (Var name), t)
typed _ e @ (Atom (Const (ConstInt n))) =
    pure (Atom $ Const $ ConstInt n, PrimType $ nameFromString "Int")

typecheck :: Expr () -> IO (Either TypeError (Expr Type, MonoType))
typecheck = runExceptT . typed Map.empty
