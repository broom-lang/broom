module Unify (Substitution, Unification, UnificationError, unify) where

import Data.List (sortBy)
import qualified Data.HashMap.Lazy as Map
import Data.Foldable (traverse_)
import Control.Monad.State.Lazy (StateT, get, modify)
import Control.Monad.Except (ExceptT, throwError, Except)

import Util (Name)
import Type (Type(..), MonoType(..), Row)

type Map = Map.HashMap

type Substitution = Map Name MonoType

data UnificationError = PolytypeUnification Type
                      | UnificationShapes MonoType MonoType
                      | RowUnificationShapes Row Row
                      | Occurs Name MonoType
                      deriving Show

type Unification a = StateT Substitution (Except UnificationError) a

unify :: Type -> Type -> Unification ()
unify (t @ (TypeForAll _ _)) _ = throwError $ PolytypeUnification t
unify _ (t @ (TypeForAll _ _)) = throwError $ PolytypeUnification t
unify (MonoType t1) (MonoType t2) = monoUnify t1 t2

monoUnify :: MonoType -> MonoType -> Unification ()
monoUnify t1 t2 =
    do t1 <- walk t1
       t2 <- walk t2
       unifyWalked t1 t2
    where unifyWalked t1 t2 | t1 == t2 = return ()
          unifyWalked (TypeVar name1) t2 = unifyVar name1 t2
          unifyWalked t1 (TypeVar name2) = unifyVar name2 t1
          unifyWalked (TypeArrow d1 cd1) (TypeArrow d2 cd2) = monoUnify d1 d2 >> monoUnify cd1 cd2
          unifyWalked (RecordType r1) (RecordType r2) = unifyRows r1 r2
          unifyWalked (DataType n1 _) (DataType n2 _) | n1 == n2 = return ()
          unifyWalked t1 t2 = throwError $ UnificationShapes t1 t2

unifyRows :: Row -> Row -> Unification ()
unifyRows r1 r2 = unifySortedRows (sortRow r1) (sortRow r2)
    where sortRow = sortBy (\(l1, _) (l2, _) -> compare l1 l2)
          unifySortedRows ((l1, t1) : r1) ((l2, t2) : r2) | l1 == l1 =
              monoUnify t1 t2 >> unifySortedRows r1 r2
          unifySortedRows r1 r2 = throwError $ RowUnificationShapes r1 r2

unifyVar :: Name -> MonoType -> Unification ()
unifyVar name t =
    do occursCheck name t
       modify (Map.insert name t)

walk :: MonoType -> Unification MonoType
walk (t @ (TypeVar name)) =
    do subst <- get
       case Map.lookup name subst of
           Just val -> walk val
           Nothing -> return t
walk t = return t

occursCheck :: Name -> MonoType -> Unification ()
occursCheck name t =
    do t <- walk t
       case t of
           TypeArrow d cd -> occursCheck name d >> occursCheck name cd
           RecordType row -> checkRow row
           DataType _ row -> checkRow row
           TypeVar name' | name' == name -> throwError $ Occurs name t
           TypeVar _ -> return ()
           PrimType _ -> return ()
    where checkRow = traverse_ (occursCheck name . snd)
