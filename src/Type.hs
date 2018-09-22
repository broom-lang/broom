module Type ( Kind(..), Type(..), MonoType(..), PrimType(..), Row
            , OpenType, ClosedType, OpenMonoType, ClosedMonoType ) where

import Data.Functor.Fixedpoint (Fix)
import Data.List (sortBy)
import Control.Unification (Unifiable(..), UTerm)
import Control.Unification.IntVar (IntVar)

import Util (Name)

data Kind = Type

data Type t = TypeForAll [Name] t
            deriving Show

data MonoType x = TypeArrow x x
                | RecordType (Row x)
                | OpaqueType Name
                | PrimType PrimType
                deriving (Show, Functor, Foldable, Traversable)

instance Unifiable MonoType where
    zipMatch (TypeArrow d1 cd1) (TypeArrow d2 cd2) =
        Just $ TypeArrow (Right (d1, d2)) (Right (cd1, cd2))
    zipMatch (RecordType r1) (RecordType r2) = RecordType <$> zipMatchRows r1 r2
    zipMatch (PrimType t1) (PrimType t2) | t1 == t2 = Just $ PrimType t1
    zipMatch _ _ = Nothing

data PrimType = TypeInt | TypeBool deriving (Show, Eq)

type Row x = [(Name, x)]

zipMatchRows :: Row a -> Row a -> Maybe (Row (Either a (a, a)))
zipMatchRows r1 r2 = zipMatchSortedRows (sortRow r1) (sortRow r2)
    where zipMatchSortedRows [] [] = Just []
          zipMatchSortedRows ((l1, t1) : ts1) ((l2, t2) : ts2) | l1 == l2 =
              ((l1, Right (t1, t2)) :) <$> zipMatchRows ts1 ts2
          zipMatchSortedRows _ _ = Nothing
          sortRow = sortBy (\(l1, _) (l2, _) -> compare l1 l2)

type OpenType = Type OpenMonoType
type ClosedType = Type ClosedMonoType

type OpenMonoType = UTerm MonoType IntVar
type ClosedMonoType = Fix MonoType
