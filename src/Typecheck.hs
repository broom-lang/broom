{-# LANGUAGE TypeApplications #-}

module Typecheck (TypeError, TypedExpr, TypedDecl, typecheck) where

import Data.Foldable (foldl')
import Data.Semigroup ((<>))
import Data.Text (Text)
import qualified Data.HashMap.Lazy as HashMap
import Data.Text.Prettyprint.Doc (Pretty, pretty, (<+>))
import Control.Eff (Eff, Member, run)
import Control.Eff.Reader.Lazy (Reader, runReader, ask, local)
import Control.Eff.Exception (Exc, runError, throwError)

import Util (Name)
import Ast (Expr(..), Decl(..), Const(..), Primop(..), Type(..), MonoType(..), typeCon)

type SrcExpr = Expr (Maybe MonoType) (Maybe Type)
type TypedExpr = Expr MonoType Type
type SrcDecl = Decl (Maybe MonoType) (Maybe Type)
type TypedDecl = Decl MonoType Type

data TypeError = Unbound Name
               | TypeMismatch MonoType MonoType
               | UnCallable SrcExpr MonoType
               | Argc Int Int

instance Pretty TypeError where
    pretty (Unbound name) = "Unbound:" <+> pretty name
    pretty (TypeMismatch t u) =
        "TypeMismatch:" <+> "expected" <+> pretty t <> ", got" <+> pretty u
    pretty (UnCallable expr t) = "Uncallable:" <+> pretty expr <> ":" <+> pretty t
    pretty (Argc goal actual) =
        "Wrong number of arguments:" <+> "expected" <+> pretty goal <>
            ", got" <+> pretty actual

newtype Ctx = Ctx (HashMap.HashMap Name Type)

builtinCtx :: Ctx
builtinCtx = Ctx HashMap.empty

ctxInsert :: Name -> Type -> Ctx -> Ctx
ctxInsert name t (Ctx bindings) = Ctx (HashMap.insert name t bindings)

ctxInsertDecls :: [SrcDecl] -> Ctx -> Ctx
ctxInsertDecls decls ctx = foldl' insertDecl ctx decls
    where insertDecl kvs (Val name (Just t) _) = ctxInsert name t kvs
          insertDecl _ (Val _ Nothing _) = error "type inference unimplemented"

ctxLookup :: Name -> Ctx -> Maybe Type
ctxLookup name (Ctx bindings) = HashMap.lookup name bindings

typecheck :: SrcExpr -> Either TypeError TypedExpr
typecheck expr = fst <$> run (runError (runReader (check expr) builtinCtx))

check :: (Member (Reader Ctx) r, Member (Exc TypeError) r)
      => SrcExpr -> Eff r (TypedExpr, MonoType)
check =
    \case Lambda param (Just domain) body ->
              local (ctxInsert param (MonoType domain))
                    (do (typedBody, codomain) <- check body
                        pure ( Lambda param domain typedBody
                             , TypeArrow domain codomain ))
          Lambda _ _ _ -> error "type inference unimplemented"
          App callee arg ->
              do (typedCallee, calleeType) <- check callee
                 case calleeType of
                     TypeArrow domain codomain ->
                         do typedArg <- checkAs domain arg
                            pure (App typedCallee typedArg, codomain)
                     _ -> throwError $ UnCallable callee calleeType
          PrimApp Add args -> checkArithmetic Add args $ typeCon @Text "Int"
          PrimApp Sub args -> checkArithmetic Sub args $ typeCon @Text "Int"
          PrimApp Mul args -> checkArithmetic Mul args $ typeCon @Text "Int"
          PrimApp Div args -> checkArithmetic Div args $ typeCon @Text "Int"
          PrimApp Eq args -> checkArithmetic Eq args $ typeCon @Text "Bool"
          Let decls body ->
              local (ctxInsertDecls decls)
                    (do typedDecls <- traverse checkDecl decls
                        (typedBody, bodyType) <- check body
                        pure (Let typedDecls typedBody, bodyType))
          If cond conseq alt ->
              do typedCond <- checkAs (typeCon @Text "Bool") cond
                 (typedConseq, resType) <- check conseq
                 typedAlt <- checkAs resType alt
                 pure (If typedCond typedConseq typedAlt, resType)
          Var name -> do maybeType <- ctxLookup name <$> ask
                         case maybeType of
                             Just (MonoType t) -> pure (Var name, t)
                             Just (TypeForAll _ _) -> error "type inference unimplemented"
                             Nothing -> throwError (Unbound name)
          Const (IntConst n) -> pure (Const (IntConst n), typeCon @Text "Int")

checkDecl :: (Member (Reader Ctx) r, Member (Exc TypeError) r)
          => SrcDecl -> Eff r TypedDecl
checkDecl (Val name (Just (MonoType t)) valueExpr) = Val name (MonoType t) <$> checkAs t valueExpr
checkDecl (Val _ _ _) = error "type inference unimplemented"

checkAs :: (Member (Reader Ctx) r, Member (Exc TypeError) r)
        => MonoType -> SrcExpr -> Eff r TypedExpr
checkAs goalType expr = do (typed, t) <- check expr
                           if t == goalType
                           then pure typed
                           else throwError (TypeMismatch goalType t)

checkArithmetic :: (Member (Reader Ctx) r, Member (Exc TypeError) r)
                => Primop -> [SrcExpr] -> MonoType -> Eff r (TypedExpr, MonoType)
checkArithmetic op [l, r] t = do typedL <- checkAs (typeCon @Text "Int") l
                                 typedR <- checkAs (typeCon @Text "Int") r
                                 pure (PrimApp op [typedL, typedR], t)
checkArithmetic _ args _ = throwError $ Argc 2 (length args)
