{-# LANGUAGE ConstraintKinds #-}

module Language.Broom.Alphatize (alphatize) where

import qualified Data.HashMap.Lazy as Env
import Data.Generics.Uniplate.Data (descendM, descendBiM)
import Data.Text.Prettyprint.Doc (Pretty, pretty, (<+>))
import Control.Eff (Eff, Member)
import Control.Eff.Reader.Lazy (Reader, runReader, local, ask)
import Control.Eff.State.Strict (State)
import Control.Eff.Exception (Exc, runError, throwError)

import Language.Broom.Util (Name, gensym)
import qualified Language.Broom.Ast as Ast
import Language.Broom.Ast (Expr(..), Stmt(..), Def(..), defName)

-- TODO: Type variables

type Env = Env.HashMap Name Def

replace :: (Member (Reader Env) r, Member (Exc Err) r) => Name -> Eff r Def
replace name = do env <- ask
                  case Env.lookup name env of
                      Just def' -> pure def'
                      Nothing -> throwError $ Unbound name

data Err = Unbound Name

instance Pretty Err where
    pretty (Unbound name) = "Unbound:" <+> pretty name

type AlphaEffs r = (Member (Reader Env) r, Member (State Int) r, Member (Exc Err) r)

alphatize :: Member (State Int) r => Ast.Expr -> Eff r (Either Err Ast.Expr)
alphatize expr = runError $ runReader (Env.empty :: Env) (alpha expr)

alpha :: AlphaEffs r => Ast.Expr -> Eff r Ast.Expr
alpha expr = case expr of
    Lambda (Def param domain) body ->
        do param' <- gensym param
           let def' = Def param' domain
           local (Env.insert param def')
                 (descendM alpha (Lambda def' body))
    App _ _ _ -> descendM alpha expr
    PrimApp _ _ _ -> descendM alpha expr
    Let decls body -> do let binders = letBinders decls
                         binders' <- traverse (\(Def name t) -> Def <$> gensym name <*> pure t)
                                              binders
                         local (Env.union (Env.fromList (zip (fmap defName binders) binders')))
                               (Let <$> traverse alphaStmt decls <*> alpha body)
    If _ _ _ _ -> descendM alpha expr
    IsA _ _ -> descendM alpha expr
    Var (Def name _) -> Var <$> replace name
    Const _ -> pure expr

alphaStmt :: AlphaEffs r => Ast.Stmt -> Eff r Ast.Stmt
alphaStmt (Val (Def name _) valueExpr) = do def' <- replace name
                                            descendBiM alpha (Val def' valueExpr)
alphaStmt decl @ (Expr _) = descendBiM alpha decl

letBinders :: [Ast.Stmt] -> [Def]
letBinders decls = decls >>= declBinder
    where declBinder (Val def _) = pure def
          declBinder (Expr _) = mempty
