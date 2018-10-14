{-# LANGUAGE ConstraintKinds #-}

module Language.Broom.Alphatize (Err, alphatize) where

import qualified Data.HashMap.Lazy as Env
import Data.Generics.Uniplate.Operations (descendM)
import Data.Text.Prettyprint.Doc (Pretty, pretty, (<+>))
import Control.Eff (Eff, Member)
import Control.Eff.Reader.Lazy (Reader, runReader, local, ask)
import Control.Eff.State.Strict (State)
import Control.Eff.Exception (Exc, runError, throwError)

import Language.Broom.Util (Name, gensym)
import qualified Language.Broom.Ast as Ast
import Language.Broom.Ast (Expr(..), Stmt(..), Def(..), defName)

-- TODO: Type variables

type Env h = Env.HashMap Name (Def h)

replace :: (Member (Reader (Env h)) r, Member (Exc Err) r) => Name -> Eff r (Def h)
replace name = do env <- ask
                  case Env.lookup name env of
                      Just def' -> pure def'
                      Nothing -> throwError $ Unbound name

data Err = Unbound Name

instance Pretty Err where
    pretty (Unbound name) = "Unbound:" <+> pretty name

type AlphaEffs h r = ( Member (Reader (Env h)) r
                     , Member (State Int) r
                     , Member (Exc Err) r )

alphatize :: forall h r . Member (State Int) r => Ast.Expr h -> Eff r (Either Err (Ast.Expr h))
alphatize expr = runError $ runReader (Env.empty :: Env h) (alpha expr)

alpha :: AlphaEffs h r => Ast.Expr h -> Eff r (Ast.Expr h)
alpha expr = case expr of
    Lambda (Def param domain) body ->
        do param' <- gensym param
           let def' = Def param' domain
           local (Env.insert param def')
                 (Lambda def' <$> alpha body)
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

alphaStmt :: AlphaEffs h r => Ast.Stmt h -> Eff r (Ast.Stmt h)
alphaStmt (Val (Def name _) valueExpr) = do def' <- replace name
                                            Val def' <$> alpha valueExpr
alphaStmt (Expr expr) = Expr <$> alpha expr

letBinders :: [Ast.Stmt h] -> [Def h]
letBinders decls = decls >>= declBinder
    where declBinder (Val def _) = pure def
          declBinder (Expr _) = mempty
