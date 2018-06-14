module Type (Type(..), MonoType(..), TypeVar, Row, readTypeVar, writeTypeVar) where

import Data.IORef (IORef, readIORef, writeIORef)

import Util (Name)

data Type = TypeForAll [Name] MonoType
          | MonoType MonoType
          deriving (Show, Eq)

data MonoType = TypeArrow MonoType MonoType
              | RecordType Row
              | DataType Name Row
              | TypeVar TypeVar
              | PrimType Name
              deriving (Show, Eq)

newtype TypeVar = TV (IORef (Maybe MonoType))
                deriving Eq

instance Show TypeVar where
    show = const "??"

readTypeVar :: TypeVar -> IO (Maybe MonoType)
readTypeVar (TV r) = readIORef r

writeTypeVar :: TypeVar -> MonoType -> IO ()
writeTypeVar (TV r) v =
    do oldValue <- readIORef r
       case oldValue of
           Nothing -> writeIORef r (Just v)
           Just _ -> error "tried to reinitialize type variable"

type Row = [(Name, MonoType)]
