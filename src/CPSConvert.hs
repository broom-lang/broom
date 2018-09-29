{-# LANGUAGE TypeApplications, ConstraintKinds #-}

module CPSConvert (Block(..), Transfer(..), Stmt(..), Expr(..), Atom(..), cpsConvert) where

import Data.Bifunctor (second)
import Data.Foldable (traverse_)
import Data.Maybe (fromJust)
import Data.Convertible (convert)
import Data.Text (Text)
import qualified Data.HashMap.Lazy as Ctx
import Control.Eff (Eff, Member)
import Control.Eff.Fresh (Fresh)
import Control.Eff.State.Lazy (State, evalState, get, modify)

import Util (Name, gensym)
import qualified Ast
import Ast (Primop(..), Const(..), primopResMonoType)
import Typecheck (TypedExpr)
import CPS ( Block(..), Stmt(..), Expr(..), Transfer(..), Atom(..), Type(..), int, bool
           , primopResType )

type Ctx = Ctx.HashMap Name Ast.MonoType

lookupMonoType :: Member (State Ctx) r => Name -> Eff r Ast.MonoType
lookupMonoType name = do ctx :: Ctx <- get
                         pure $ fromJust (Ctx.lookup name ctx)

lookupType :: Member (State Ctx) r => Name -> Eff r Type
lookupType name = convert <$> lookupMonoType name

class CPSTypable a where
    typeOf :: Member (State Ctx) r => a -> Eff r Type

instance CPSTypable TypedExpr where
    typeOf expr = convert <$> monoTypeOf expr

instance CPSTypable Expr where
    typeOf = \case Fn params _ -> pure $ FnType (fmap snd params)
                   PrimApp op _ -> pure (primopResType op)
                   Atom a -> typeOf a

instance CPSTypable Atom where
    typeOf = \case Use name -> lookupType name
                   Const c -> typeOf c

instance CPSTypable Const where
    typeOf = \case IntConst _ -> pure $ TypeName (convert @Text "Int")

-- OPTIMIZE
monoTypeOf :: Member (State Ctx) r => TypedExpr -> Eff r Ast.MonoType
monoTypeOf = \case Ast.Lambda [(_, domain)] body ->
                       do codomain <- monoTypeOf body
                          pure $ Ast.TypeArrow domain codomain
                   Ast.App callee _ -> monoTypeOf callee >>= \case
                       Ast.TypeArrow _ codomain -> pure codomain
                       _ -> error "unreachable"
                   Ast.PrimApp op _ -> pure (primopResMonoType op)
                   Ast.Let _ body -> monoTypeOf body
                   Ast.If _ conseq _ -> monoTypeOf conseq
                   Ast.Var name -> lookupMonoType name
                   Ast.Const (IntConst _) -> pure (Ast.typeCon @Text "Int")

cpsConvert :: Member Fresh r => TypedExpr -> Eff r Expr
cpsConvert expr = evalState (evalState m ([[]] :: BlockBuilders)) (Ctx.empty :: Ctx)
    where m = do halt <- gensym (convert @Text "halt")
                 Fn [(halt, FnType [int])] <$> conv (TrivCont halt) expr

type BlockBuilder = [Stmt]
type BlockBuilders = [BlockBuilder]

pushStmt :: (Member (State BlockBuilders) r) => Stmt -> Eff r ()
pushStmt stmt = modify (\(stmts : builders) -> (stmt : stmts) : builders)

pushBlock :: (Member (State BlockBuilders) r) => Eff r ()
pushBlock = modify (\builders -> [] : builders :: BlockBuilders)

popBlock :: (Member (State BlockBuilders) r) => Transfer -> Eff r Block
popBlock transfer = do (stmts : _) <- get
                       modify (\(_ : builders :: BlockBuilders) -> builders)
                       pure $ Block (reverse stmts) transfer

data Cont r = ContFn Type (Expr -> Eff r Block)
            | TrivCont Name

continue :: ConversionEffs r => Cont r -> Expr -> Eff r Block
continue (ContFn _ k) expr = k expr
continue (TrivCont k) expr = do aExpr <- trivialize expr
                                popBlock $ App k [aExpr]

type ConversionEffs r = (Member Fresh r, Member (State BlockBuilders) r, Member (State Ctx) r)

conv :: ConversionEffs r => Cont r -> TypedExpr -> Eff r Block
conv cont = \case
    Ast.Lambda params body ->
        do traverse_ (\(name, t) -> modify (Ctx.insert name t)) params
           ret <- gensym (convert @Text "r")
           let params' = fmap (second convert) params
           bodyType <- typeOf body
           pushBlock
           cpsBody <- conv (TrivCont ret) body
           continue cont $ Fn ((ret, FnType [bodyType]) : params') cpsBody
    Ast.App callee args ->
        do ret <- nominalizeCont cont
           calleeType <- typeOf callee
           let cont' = ContFn calleeType $ \cpsCallee ->
                   do aCallee <- nominalize cpsCallee
                      let k = \aArgs -> popBlock $ App aCallee (Use ret : aArgs)
                      convArgs k args
           conv cont' callee
    Ast.PrimApp op args ->
        let k = \aArgs -> continue cont (PrimApp op aArgs)
        in convArgs k args
    Ast.Let (Ast.Val name (Ast.MonoType t) expr : decls) body ->
        do modify (Ctx.insert name t)
           let t' = convert t
               cont' = ContFn t' $ \cpsExpr ->
                   do pushStmt $ Def name t' cpsExpr
                      conv cont $ Ast.Let decls body
           conv cont' expr
    Ast.Let [] body -> conv cont body
    Ast.If cond conseq alt ->
        do k <- TrivCont <$> nominalizeCont cont
           let cont' = ContFn bool $ \cpsCond ->
                   do aCond <- trivialize cpsCond
                      pushBlock
                      conseqBlock <- conv k conseq
                      pushBlock
                      altBlock <- conv k alt
                      popBlock $ If aCond conseqBlock altBlock
           conv cont' cond
    Ast.Var name -> continue cont (Atom (Use name))
    Ast.Const c -> continue cont (Atom (Const c))

convArgs :: forall r . ConversionEffs r => ([Atom] -> Eff r Block) -> [TypedExpr] -> Eff r Block
convArgs cont arguments = loop arguments []
    where loop [] aArgs = cont (reverse aArgs)
          loop (arg : args) aArgs =
              do argType <- typeOf arg
                 let cont' :: Cont r
                     cont' = ContFn argType $ \cpsArg ->
                         do aArg <- trivialize cpsArg
                            loop args (aArg : aArgs)
                 conv cont' arg

nominalize :: ConversionEffs r => Expr -> Eff r Name
nominalize = \case
    Atom (Use name) -> pure name
    expr -> do name <- gensym (convert @Text "v")
               t <- typeOf expr
               pushStmt $ Def name t expr
               pure name

nominalizeCont :: ConversionEffs r => Cont r -> Eff r Name
nominalizeCont = \case ContFn paramType k ->
                           do param <- gensym (convert @Text "x")
                              pushBlock
                              body <- k (Atom (Use param))
                              nominalize $ Fn [(param, paramType)] body
                       TrivCont k -> pure k

trivialize :: ConversionEffs r => Expr -> Eff r Atom
trivialize = \case Atom a -> pure a
                   expr -> Use <$> nominalize expr
