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
import Language.Broom.Cst (Primop(..), Type(..), TypeAtom(..), PrimType(..))
import qualified Language.Broom.Ast as Ast
import Language.Broom.Ast (Expr(..), Stmt(..), Def(..))

data Err = Unbound Name

instance Pretty Err where
    pretty (Unbound name) = "Unbound:" <+> pretty name

linearize :: Expr -> Either Err Expr
linearize expr = runST $ runLift $ do env :: Env s <- lift Env.new
                                      runReader env (analyzeVars expr)
                                      runError $ runReader env (linearized expr)

data BindKind = Linear | Recursive Def

data Occurrence = Param | Declare | Use

type Env s = Env.HashTable s Name BindKind

type AnaEffs s r = (Member (Reader (Env s)) r, Lifted (ST s) r)

updateBindKind :: AnaEffs s r => Occurrence -> Def -> Eff r ()
updateBindKind occ (Def name t) = do env :: Env s <- ask
                                     lift $ Env.mutate env name ((, ()) . updated)
    where updated Nothing =
              Just $ case occ of
                         Param -> Linear
                         Declare -> Linear
                         Use -> Recursive $ Def name (TypeApp (TAtom $ PrimType VarBox) t)
          updated old = old

-- Collect the BindKinds of each variable into the `Env s` in the Reader:
analyzeVars :: AnaEffs s r => Expr -> Eff r ()
analyzeVars expr = case expr of
    Lambda def body -> updateBindKind Param def *> analyzeVars body
    App callee arg _ -> analyzeVars callee *> analyzeVars arg
    PrimApp _ args _ -> traverse_ analyzeVars args
    Let decls body -> traverse_ analyzeStmtVars decls *> analyzeVars body
    If cond conseq alt _ -> analyzeVars cond *> analyzeVars conseq *> analyzeVars alt
    IsA expr' _ -> analyzeVars expr'
    Var def -> updateBindKind Use def
    Const _ -> pure ()

analyzeStmtVars :: AnaEffs s r => Ast.Stmt -> Eff r ()
analyzeStmtVars = \case
    Val def valueExpr -> analyzeVars valueExpr *> updateBindKind Declare def
    Expr expr -> analyzeVars expr

type ApplyEffs s r = (Member (Exc Err) r, Member (Reader (Env s)) r, Lifted (ST s) r)

bindKindOf :: ApplyEffs s r => Name -> Eff r BindKind
bindKindOf name = ask >>= lift . flip Env.lookup name >>= \case
    Just bindKind -> pure bindKind
    Nothing -> throwError $ Unbound name

emitLoad :: ApplyEffs s r => Def -> Eff r Expr
emitLoad def @(Def name t) = bindKindOf name >>= \case
    Linear -> pure (Var def)
    Recursive boxDef -> pure $ PrimApp VarLoad [Var boxDef] t

-- OPTIMIZE: "Fixing Letrec" or some trivial variant thereof.
-- Transform `Let`:s so that `BindKind.Recursive` variables get allocated, initialized and
-- dereferenced explicitly:
linearized :: ApplyEffs s r => Expr -> Eff r Expr
linearized = transformM replace
    where replace expr = case expr of
              Lambda _ _ -> pure expr
              App _ _ _ -> pure expr
              PrimApp _ _ _ -> pure expr
              Let stmts body ->
                  do (declares, stmts') <- bimap reverse reverse <$> foldM linearizeStmt
                                                                           ([], []) stmts
                     pure $ Let (declares <> stmts') body
              If _ _ _ _ -> pure expr
              IsA _ _ -> pure expr
              Var name -> emitLoad name
              Const _ -> pure expr
          linearizeStmt (creates, stmts) stmt @ (Val (Def name _) valueExpr) =
              bindKindOf name >>= \case
                  Linear -> pure (creates, stmt : stmts)
                  Recursive boxDef @ (Def _ boxType) ->
                      let creation = Val boxDef (PrimApp VarNew [] boxType)
                          initialization = Expr $ PrimApp VarInit [Var boxDef, valueExpr]
                                                          (TAtom $ PrimType TypeUnit)
                      in pure (creation : creates, initialization : stmts)
          linearizeStmt (creates, stmts) stmt @ (Expr _) = pure (creates, stmt : stmts)
