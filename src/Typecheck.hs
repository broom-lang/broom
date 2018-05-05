module Typecheck (typeOf, emptyCtx) where

import Data.Maybe (fromJust)

import Ast (Expr(..), Type(..), Atom(..), Const(..))

newtype Ctx = Ctx [(String, Type)]

emptyCtx :: Ctx
emptyCtx = Ctx []

typeOf :: Ctx -> Expr -> Type
typeOf (Ctx ctx) (Lambda param paramType body) =
    TypeArrow paramType (typeOf (Ctx ((param, paramType):ctx)) body)
typeOf ctx (App f arg) =
    let TypeArrow domain codomain = typeOf ctx f
    in  if typeOf ctx arg == domain
        then codomain
        else error "TypeError"
typeOf (Ctx ctx) (Atom atom) =
    case atom of
        Var name -> fromJust (lookup name ctx)
        Const (ConstInt _) -> PrimType "Int"
