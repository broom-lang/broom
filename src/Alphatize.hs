module Alphatize (alphatize) where

import Data.Maybe (fromJust)
import qualified Data.HashMap.Lazy as Env
import Control.Eff (Eff, Member, run)
import Control.Eff.Reader.Lazy (Reader, runReader, local, ask)
import Control.Eff.Fresh (Fresh, runFresh')

import Util (Name, gensym)
import Ast (Expr(..), Decl(..))
import Typecheck (TypedExpr, TypedDecl)

type Env = Env.HashMap Name Name

type Alphatization a = forall r . (Member (Reader Env) r, Member Fresh r) => Eff r a

alphatize :: TypedExpr -> TypedExpr
alphatize expr = run $ runReader (runFresh' (alpha expr) 0) (Env.empty :: Env)

alpha :: TypedExpr -> Alphatization TypedExpr
alpha =
    \case Lambda param _ body -> do param' <- gensym param
                                    local (Env.insert param param')
                                          (alpha body)
          App callee arg -> App <$> alpha callee <*> alpha arg
          PrimApp op args -> PrimApp op <$> traverse alpha args
          Let decls body -> do let binders = letBinders decls
                               binders' <- traverse gensym binders
                               local (Env.union (Env.fromList (zip binders binders')))
                                     (Let <$> traverse alphaDecl decls <*> alpha body)
          If cond conseq alt -> If <$> alpha cond <*> alpha conseq <*> alpha alt
          Var name -> do env :: Env <- ask
                         -- fromJust is fine since name cannot be unbound after type checking:
                         return $ Var (fromJust (Env.lookup name env))
          c @ (Const _) -> pure c

alphaDecl :: TypedDecl -> Alphatization TypedDecl
alphaDecl (Val name t valueExpr) =
    do env <- ask
       Val (fromJust (Env.lookup name env)) t <$> alpha valueExpr

letBinders :: [TypedDecl] -> [Name]
letBinders decls = fmap declBinder decls
    where declBinder (Val name _ _) = name
