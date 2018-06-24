module Unify (UnificationError, Unification, unify) where

import Data.List (sortBy)
import Data.Foldable (traverse_)
import Control.Monad.Except (ExceptT, throwError, liftIO)

import Util (Name)
import Type (MonoType(..), TypeVar, Row, readTypeVar, writeTypeVar)

data UnificationError = InEqNames MonoType MonoType
                      | InEqLabels Name Name
                      | TypeShapes MonoType MonoType
                      | Occurs TypeVar
                      deriving Show

type Unification a = ExceptT UnificationError IO a

unify :: MonoType -> MonoType -> Unification ()
unify t1 t2 = do t1 <- walk t1
                 t2 <- walk t2
                 unifyWalked t1 t2

unifyWalked :: MonoType -> MonoType -> Unification ()
unifyWalked (TypeArrow d1 c1) (TypeArrow d2 c2) = unify d1 d2 *> unify c1 c2
unifyWalked (RecordType r1) (RecordType r2) = unifyRows r1 r2
unifyWalked t1 @ (DataType n1 _) t2 @ (DataType n2 _) =
    if n1 == n2 then pure () else throwError $ InEqNames t1 t2
unifyWalked t1 @ (TypeVar r1) t2 @ (TypeVar r2) =
    if r1 == r2 then pure () else defineVar r1 t2
unifyWalked (TypeVar r) t = defineVar r t
unifyWalked t (TypeVar r) = defineVar r t
unifyWalked t1 @ (TypeName name1) t2 @ (TypeName name2) =
    if name1 == name2 then pure () else throwError $ InEqNames t1 t2
unifyWalked t1 @ (PrimType n1) t2 @ (PrimType n2) =
    if n1 == n2 then pure () else throwError $ InEqNames t1 t2
unifyWalked t1 t2 = throwError $ TypeShapes t1 t2

defineVar :: TypeVar -> MonoType -> Unification ()
defineVar r t = occursCheck r t >> liftIO (writeTypeVar r t)
    where occursCheck :: TypeVar -> MonoType -> Unification ()
          occursCheck v (TypeArrow d c) = occursCheck v d >> occursCheck v c
          occursCheck v (RecordType r) = traverse_ (occursCheck v . snd) r
          occursCheck v (DataType _ r) = traverse_ (occursCheck v . snd) r
          occursCheck v (TypeVar v') | v == v' = throwError $ Occurs v
          occursCheck _ (TypeVar _) = pure ()
          occursCheck _ (TypeName _) = pure ()
          occursCheck _ (PrimType _) = pure ()

unifyRows :: Row -> Row -> Unification ()
unifyRows r1 r2 = unifySorted (sortRow r1) (sortRow r2)
    where sortRow = sortBy (\(l1, _) (l2, _) -> compare l1 l2)
          unifySorted ((l1, t1) : r1) ((l2, t2) : r2) =
              if l1 == l2
              then unify t1 t2 >> unifySorted r1 r2
              else throwError $ InEqLabels l1 l2

-- Reduces `t` to a nonvariable or an uninitialized variable
walk :: MonoType -> Unification MonoType
walk t @ (TypeVar r) = do ot' <- liftIO $ readTypeVar r
                          case ot' of
                              Just t' -> walk t'
                              Nothing -> return t
walk t = pure t
