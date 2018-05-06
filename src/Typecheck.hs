module Typecheck (typeOf, emptyCtx) where

import Data.Maybe (fromJust)

import Ast (Expr(..), Type(..), Atom(..), Const(..))

newtype Ctx = Ctx [(String, Type)]

emptyCtx :: Ctx
emptyCtx = Ctx []

ctxInsert :: Ctx -> String -> Type -> Ctx
ctxInsert (Ctx bindings) name typ = Ctx $ (name, typ) : bindings

ctxLookup :: String -> Ctx -> Maybe Type
ctxLookup name (Ctx bindings) = lookup name bindings

typeOf :: Ctx -> Expr -> Type
typeOf ctx (Lambda param paramType body) =
    let ctx' = ctxInsert ctx param paramType
    in  TypeArrow paramType (typeOf ctx' body)
typeOf ctx (App f arg) =
    let TypeArrow domain codomain = typeOf ctx f
    in  if typeOf ctx arg == domain
        then codomain
        else error "TypeError"
typeOf ctx (Let name typ expr body) =
    if typeOf ctx expr == typ
    then let ctx' = ctxInsert ctx name typ
         in  typeOf ctx' body
    else error "TypeError"
typeOf ctx (Atom atom) =
    case atom of
        Var name -> fromJust (ctxLookup name ctx)
        Const (ConstInt _) -> PrimType "Int"
