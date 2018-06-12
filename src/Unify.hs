module Unify (Substitution, Unification, UnificationError, unify) where

import qualified Data.HashMap.Lazy as Map
import Data.Unique (Unique)
import Data.Foldable (traverse_)
import Control.Monad.State.Lazy (StateT, get, modify)
import Control.Monad.Except (ExceptT, throwError, Except)

import Ast (Type(..))

type Map = Map.HashMap

type Substitution = Map Unique Type

data UnificationError = PolytypeUnification Type
                      | UnificationShapes Type Type
                      | Occurs Unique Type
                      deriving Show

type Unification a = StateT Substitution (Except UnificationError) a

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
       modify (Map.insert name t)

walk :: Type -> Unification Type
walk (t @ (TypeVar name)) =
    do subst <- get
       case Map.lookup name subst of
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
