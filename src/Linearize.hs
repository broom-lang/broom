{-# LANGUAGE ConstraintKinds #-}

module Linearize (Err, linearize) where

import qualified Data.HashTable.ST.Basic as Env
import Data.Text.Prettyprint.Doc (Pretty, pretty, (<+>))
import Control.Monad.ST (ST, runST)
import Control.Eff (Eff, Member)
import Control.Eff.Exception (Exc, runError)
import Control.Eff.Reader.Strict (Reader, runReader)
import Control.Eff.Lift (Lifted, runLift, lift)

import Util (Name)
import Typecheck (TypedExpr)

data Err = Unbound Name

instance Pretty Err where
    pretty (Unbound name) = "Unbound:" <+> pretty name
    
linearize :: TypedExpr -> Either Err TypedExpr
linearize expr = runST $ runLift $ do env :: Env s <- lift Env.new
                                      runReader env (analyzeVars expr)
                                      runError $ runReader env (linearized expr)

data BindKind = Linear | Recursive

type Env s = Env.HashTable s Name BindKind

type AnaEffs s r = (Member (Reader (Env s)) r, Lifted (ST s) r)

-- Collect the BindKinds of each variable into the `Env s` in the Reader:
analyzeVars :: AnaEffs s r => TypedExpr -> Eff r ()
analyzeVars = undefined

type ApplyEffs s r = (Member (Exc Err) r, Member (Reader (Env s)) r, Lifted (ST s) r)

-- OPTIMIZE: "Fixing Letrec" or some trivial variant thereof.
-- Transform `Let`:s so that `BindKind.Recursive` variables get allocated, initialized and
-- dereferenced explicitly:
linearized :: ApplyEffs s r => TypedExpr -> Eff r TypedExpr
linearized = undefined
