module Language.Broom.Typecheck (TypeError, Expr, Stmt, typecheck) where

import Data.Foldable (foldl')
import Data.Semigroup ((<>))
import qualified Data.HashMap.Lazy as HashMap
import Data.Text.Prettyprint.Doc (Pretty, pretty, (<+>))
import Control.Eff (Eff, Member, run)
import Control.Eff.Reader.Lazy (Reader, runReader, ask, local)
import Control.Eff.Exception (Exc, runError, throwError)

import Language.Broom.Util (Name)
import qualified Language.Broom.Cst as Cst
import Language.Broom.Cst (Const(..), Primop(..), Type(..), PrimType(..), primopResType)
import Language.Broom.Ast (Expr(..), Stmt(..))

data TypeError = Unbound Name
               | TypeMismatch Type Type
               | UnCallable Cst.Expr Type
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

ctxInsertStmts :: [Cst.Stmt] -> Ctx -> Ctx
ctxInsertStmts decls ctx = foldl' insertStmt ctx decls
    where insertStmt kvs (Cst.Val name (Just t) _) = ctxInsert name t kvs
          insertStmt _ (Cst.Val _ Nothing _) = error "type inference unimplemented"
          insertStmt kvs (Cst.Expr _) = kvs

ctxLookup :: Name -> Ctx -> Maybe Type
ctxLookup name (Ctx bindings) = HashMap.lookup name bindings

typecheck :: Cst.Expr -> Either TypeError Expr
typecheck expr = fst <$> run (runError (runReader builtinCtx (check expr)))

check :: (Member (Reader Ctx) r, Member (Exc TypeError) r)
      => Cst.Expr -> Eff r (Expr, Type)
check =
    \case Cst.Lambda param (Just domain) body ->
              local (ctxInsert param domain)
                    (do (typedBody, codomain) <- check body
                        pure ( Lambda param domain (IsA typedBody codomain)
                             , TypeArrow domain codomain ))
          Cst.Lambda _ Nothing _ -> error "type inference unimplemented"
          Cst.App callee arg ->
              do (typedCallee, calleeType) <- check callee
                 case calleeType of
                     TypeArrow domain codomain ->
                         do typedArg <- checkAs domain arg
                            pure (IsA (App typedCallee typedArg) codomain, codomain)
                     _ -> throwError $ UnCallable callee calleeType
          -- OPTIMIZE:
          Cst.PrimApp op args -> do argTypes <- map snd <$> traverse check args
                                    checkArithmetic op args (primopResType op argTypes)
          Cst.Let decls body ->
              local (ctxInsertStmts decls)
                    (do typedStmts <- traverse checkStmt decls
                        (typedBody, bodyType) <- check body
                        pure (Let typedStmts (IsA typedBody bodyType), bodyType))
          Cst.If cond conseq alt ->
              do typedCond <- checkAs (PrimType TypeBool) cond
                 (typedConseq, resType) <- check conseq
                 typedAlt <- checkAs resType alt
                 pure (IsA (If typedCond typedConseq typedAlt) resType, resType)
          Cst.IsA expr t -> (,t) . flip IsA t <$> checkAs t expr
          Cst.Var name -> do maybeType <- ctxLookup name <$> ask
                             case maybeType of
                                 Just t -> pure (Var name, t)
                                 Nothing -> throwError (Unbound name)
          Cst.Const (IntConst n) -> pure (Const (IntConst n), PrimType TypeInt)
          Cst.Const UnitConst -> pure (Const UnitConst, PrimType TypeUnit)

checkStmt :: (Member (Reader Ctx) r, Member (Exc TypeError) r)
          => Cst.Stmt -> Eff r Stmt
checkStmt (Cst.Val name (Just t) valueExpr) = Val name t <$> checkAs t valueExpr
checkStmt (Cst.Val _ _ _) = error "type inference unimplemented"
checkStmt (Cst.Expr expr) = Expr <$> checkAs (PrimType TypeUnit) expr

checkAs :: (Member (Reader Ctx) r, Member (Exc TypeError) r)
        => Type -> Cst.Expr -> Eff r Expr
checkAs goalType expr = do (typed, t) <- check expr
                           if t == goalType -- HACK
                           then pure typed
                           else throwError (TypeMismatch goalType t)

checkArithmetic :: (Member (Reader Ctx) r, Member (Exc TypeError) r)
                => Primop -> [Cst.Expr] -> Type -> Eff r (Expr, Type)
checkArithmetic op [l, r] t = do typedL <- checkAs (PrimType TypeInt) l
                                 typedR <- checkAs (PrimType TypeInt) r
                                 pure (IsA (PrimApp op [typedL, typedR]) t, t)
checkArithmetic _ args _ = throwError $ Argc 2 (length args)
