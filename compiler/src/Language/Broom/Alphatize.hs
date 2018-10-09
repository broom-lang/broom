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
import Language.Broom.Ast (Expr(..), Decl(..))
import Language.Broom.Typecheck (TypedExpr, TypedDecl)

type Env = Env.HashMap Name Name

replace :: (Member (Reader Env) r, Member (Exc Err) r) => Name -> Eff r Name
replace name = do env <- ask
                  case Env.lookup name env of
                      Just name' -> pure name'
                      Nothing -> throwError $ Unbound name

data Err = Unbound Name

instance Pretty Err where
    pretty (Unbound name) = "Unbound:" <+> pretty name

type AlphaEffs r = (Member (Reader Env) r, Member (State Int) r, Member (Exc Err) r)

alphatize :: Member (State Int) r => TypedExpr -> Eff r (Either Err TypedExpr)
alphatize expr = runError $ runReader (Env.empty :: Env) (alpha expr)

alpha :: AlphaEffs r => TypedExpr -> Eff r TypedExpr
alpha expr = case expr of
    Lambda param paramType body -> do param' <- gensym param
                                      local (Env.insert param param')
                                            (descendM alpha (Lambda param' paramType body))
    App _ _ -> descendM alpha expr
    PrimApp _ _ -> descendM alpha expr
    Let decls body -> do let binders = letBinders decls
                         binders' <- traverse gensym binders
                         local (Env.union (Env.fromList (zip binders binders')))
                               (Let <$> traverse alphaDecl decls <*> alpha body)
    If _ _ _ -> descendM alpha expr
    Var name -> Var <$> replace name
    Const _ -> pure expr

alphaDecl :: AlphaEffs r => TypedDecl -> Eff r TypedDecl
alphaDecl (Val name t valueExpr) = do name' <- replace name
                                      descendBiM alpha (Val name' t valueExpr)
alphaDecl decl @ (Expr _) = descendBiM alpha decl

letBinders :: [TypedDecl] -> [Name]
letBinders decls = decls >>= declBinder
    where declBinder (Val name _ _) = pure name
          declBinder (Expr _) = mempty
