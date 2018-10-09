{-# LANGUAGE ConstraintKinds #-}

module Language.Broom.Linearize (Err, linearize) where

import qualified Data.HashTable.ST.Basic as Env
import Data.Text.Prettyprint.Doc (Pretty, pretty, (<+>))
import Data.Bifunctor (bimap)
import Data.Foldable (traverse_)
import Data.Generics.Uniplate.Data (transformM)
import Control.Monad (foldM)
import Control.Monad.ST (ST, runST)
import Control.Eff (Eff, Member)
import Control.Eff.Exception (Exc, runError, throwError)
import Control.Eff.Reader.Strict (Reader, runReader, ask)
import Control.Eff.Lift (Lifted, runLift, lift)

import Language.Broom.Util (Name)
import Language.Broom.Ast(Expr(..), Decl(..), Primop(..), Type(..), PrimType(..))
import Language.Broom.Typecheck (TypedExpr, TypedDecl)

data Err = Unbound Name

instance Pretty Err where
    pretty (Unbound name) = "Unbound:" <+> pretty name

linearize :: TypedExpr -> Either Err TypedExpr
linearize expr = runST $ runLift $ do env :: Env s <- lift Env.new
                                      runReader env (analyzeVars expr)
                                      runError $ runReader env (linearized expr)

data BindKind = Linear | Recursive

data Occurrence = Param | Declare | Use

type Env s = Env.HashTable s Name BindKind

type AnaEffs s r = (Member (Reader (Env s)) r, Lifted (ST s) r)

updateBindKind :: AnaEffs s r => Occurrence -> Name -> Eff r ()
updateBindKind occ name = do env :: Env s <- ask
                             lift $ Env.mutate env name ((, ()) . updated)
    where updated Nothing = Just $ case occ of
                                       Param -> Linear
                                       Declare -> Linear
                                       Use -> Recursive
          updated old = old

-- Collect the BindKinds of each variable into the `Env s` in the Reader:
analyzeVars :: AnaEffs s r => TypedExpr -> Eff r ()
analyzeVars expr = case expr of
    Lambda param _ body -> updateBindKind Param param *> analyzeVars body
    App callee arg -> analyzeVars callee *> analyzeVars arg
    PrimApp _ args -> traverse_ analyzeVars args
    Let decls body -> traverse_ analyzeDeclVars decls *> analyzeVars body
    If cond conseq alt -> analyzeVars cond *> analyzeVars conseq *> analyzeVars alt
    IsA expr' _ -> analyzeVars expr'
    Var name -> updateBindKind Use name
    Const _ -> pure ()

analyzeDeclVars :: AnaEffs s r => TypedDecl -> Eff r ()
analyzeDeclVars = \case
    Val name _ valueExpr -> analyzeVars valueExpr *> updateBindKind Declare name
    Expr expr -> analyzeVars expr

type ApplyEffs s r = (Member (Exc Err) r, Member (Reader (Env s)) r, Lifted (ST s) r)

bindKindOf :: ApplyEffs s r => Name -> Eff r BindKind
bindKindOf name = ask >>= lift . flip Env.lookup name >>= \case
    Just bindKind -> pure bindKind
    Nothing -> throwError $ Unbound name

emitLoad :: ApplyEffs s r => Name -> Eff r TypedExpr
emitLoad name = bindKindOf name >>= \case
    Linear -> pure (Var name)
    Recursive -> pure $ IsA (PrimApp VarLoad [Var name]) (PrimType TypeInt) -- FIXME

-- OPTIMIZE: "Fixing Letrec" or some trivial variant thereof.
-- Transform `Let`:s so that `BindKind.Recursive` variables get allocated, initialized and
-- dereferenced explicitly:
linearized :: ApplyEffs s r => TypedExpr -> Eff r TypedExpr
linearized = transformM replace
    where replace expr = case expr of
              Lambda _ _ _ -> pure expr
              App _ _ -> pure expr
              PrimApp _ _ -> pure expr
              Let stmts body ->
                  do (declares, stmts') <- bimap reverse reverse <$> foldM linearizeStmt
                                                                           ([], []) stmts
                     pure $ Let (declares <> stmts') body
              If _ _ _ -> pure expr
              IsA _ _ -> pure expr
              Var name -> emitLoad name
              Const _ -> pure expr
          linearizeStmt (creates, stmts) stmt @ (Val name t valueExpr) =
              bindKindOf name >>= \case
                  Linear -> pure (creates, stmt : stmts)
                  Recursive -> let creation = Val name (TypeApp (PrimType VarBox) t)
                                                       (PrimApp VarNew [])
                                   initialization = Expr (PrimApp VarInit [Var name, valueExpr])
                               in pure (creation : creates, initialization : stmts)
          linearizeStmt (creates, stmts) stmt @ (Expr _) = pure (creates, stmt : stmts)
