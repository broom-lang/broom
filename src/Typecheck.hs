module Typecheck (TypeError, Typing, typecheck) where

import qualified Data.HashMap.Lazy as Map
import Control.Monad.Except (ExceptT, runExceptT)

import Util (Name, nameFromString)
import Ast (Expr(..), Atom(..), Const(..))
import Type (Type(..), MonoType(..))
import Unify (UnificationError)

type Ctx = Map.HashMap Name Type

data TypeError = UnificationError UnificationError
               deriving Show

type Typing a = ExceptT TypeError IO a

typed :: Ctx -> Expr () -> Typing (Expr Type, Type)
typed _ e @ (Atom (Const (ConstInt n))) =
    pure (Atom $ Const $ ConstInt n, MonoType $ PrimType $ nameFromString "Int")

typecheck :: Expr () -> IO (Either TypeError (Expr Type, Type))
typecheck = runExceptT . typed Map.empty
