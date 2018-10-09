module Language.Broom.Typecheck (TypeError, TypedExpr, TypedDecl, typecheck) where

import Data.Foldable (foldl')
import Data.Semigroup ((<>))
import qualified Data.HashMap.Lazy as HashMap
import Data.Text.Prettyprint.Doc (Pretty, pretty, (<+>))
import Control.Eff (Eff, Member, run)
import Control.Eff.Reader.Lazy (Reader, runReader, ask, local)
import Control.Eff.Exception (Exc, runError, throwError)

import Language.Broom.Util (Name)
import Language.Broom.Ast ( Expr(..), Decl(..), Const(..), Primop(..), Type(..), PrimType(..)
                          , primopResType )

type SrcExpr = Expr (Maybe Type)
type TypedExpr = Expr Type
type SrcDecl = Decl (Maybe Type)
type TypedDecl = Decl Type

data TypeError = Unbound Name
               | TypeMismatch Type Type
               | UnCallable SrcExpr Type
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
          insertDecl kvs (Expr _) = kvs

ctxLookup :: Name -> Ctx -> Maybe Type
ctxLookup name (Ctx bindings) = HashMap.lookup name bindings

typecheck :: SrcExpr -> Either TypeError TypedExpr
typecheck expr = fst <$> run (runError (runReader builtinCtx (check expr)))

check :: (Member (Reader Ctx) r, Member (Exc TypeError) r)
      => SrcExpr -> Eff r (TypedExpr, Type)
check =
    \case Lambda param (Just domain) body ->
              local (ctxInsert param domain)
                    (do (typedBody, codomain) <- check body
                        pure ( Lambda param domain (IsA typedBody codomain)
                             , TypeArrow domain codomain ))
          Lambda _ Nothing _ -> error "type inference unimplemented"
          App callee arg ->
              do (typedCallee, calleeType) <- check callee
                 case calleeType of
                     TypeArrow domain codomain ->
                         do typedArg <- checkAs domain arg
                            pure (IsA (App typedCallee typedArg) codomain, codomain)
                     _ -> throwError $ UnCallable callee calleeType
          -- OPTIMIZE:
          PrimApp op args -> do argTypes <- map snd <$> traverse check args
                                checkArithmetic op args (primopResType op argTypes)
          Let decls body ->
              local (ctxInsertDecls decls)
                    (do typedDecls <- traverse checkDecl decls
                        (typedBody, bodyType) <- check body
                        pure (Let typedDecls (IsA typedBody bodyType), bodyType))
          If cond conseq alt ->
              do typedCond <- checkAs (PrimType TypeBool) cond
                 (typedConseq, resType) <- check conseq
                 typedAlt <- checkAs resType alt
                 pure (IsA (If typedCond typedConseq typedAlt) resType, resType)
          IsA expr t -> (,t) . flip IsA t <$> checkAs t expr
          Var name -> do maybeType <- ctxLookup name <$> ask
                         case maybeType of
                             Just t -> pure (Var name, t)
                             Nothing -> throwError (Unbound name)
          Const (IntConst n) -> pure (Const (IntConst n), PrimType TypeInt)
          Const UnitConst -> pure (Const UnitConst, PrimType TypeUnit)

checkDecl :: (Member (Reader Ctx) r, Member (Exc TypeError) r)
          => SrcDecl -> Eff r TypedDecl
checkDecl (Val name (Just t) valueExpr) = Val name t <$> checkAs t valueExpr
checkDecl (Val _ _ _) = error "type inference unimplemented"
checkDecl (Expr expr) = Expr <$> checkAs (PrimType TypeUnit) expr

checkAs :: (Member (Reader Ctx) r, Member (Exc TypeError) r)
        => Type -> SrcExpr -> Eff r TypedExpr
checkAs goalType expr = do (typed, t) <- check expr
                           if t == goalType -- HACK
                           then pure typed
                           else throwError (TypeMismatch goalType t)

checkArithmetic :: (Member (Reader Ctx) r, Member (Exc TypeError) r)
                => Primop -> [SrcExpr] -> Type -> Eff r (TypedExpr, Type)
checkArithmetic op [l, r] t = do typedL <- checkAs (PrimType TypeInt) l
                                 typedR <- checkAs (PrimType TypeInt) r
                                 pure (IsA (PrimApp op [typedL, typedR]) t, t)
checkArithmetic _ args _ = throwError $ Argc 2 (length args)
