{-# LANGUAGE TypeApplications, ConstraintKinds #-}

module CPSConvert (STEff, cpsConvert) where

import Data.Bifunctor (second)
import Data.Foldable (traverse_)
import Data.Convertible (convert)
import Data.Text (Text)
import Data.STRef.Strict (STRef, newSTRef, modifySTRef, readSTRef)
import qualified Data.HashTable.ST.Basic as Ctx
import Control.Monad.ST.Strict (ST)
import Control.Eff (Eff, Member, SetMember)
import Control.Eff.State.Strict (State)
import Control.Eff.Reader.Strict (Reader, runReader, local, ask)
import Control.Eff.Lift (Lift, lift)

import Util (Name, gensym)
import qualified Ast
import Ast (Const(..))
import Typecheck (TypedExpr)
import CPS ( Block(..), Stmt(..), Expr(..), Transfer(..), Atom(..), Type(..), int, bool
           , primopResType )

type STEff s r = SetMember Lift (Lift (ST s)) r

-- Type Context for generating type annotations

type Ctx s = Ctx.HashTable s Name Type

emptyCtx :: STEff s r => Eff r (Ctx s)
emptyCtx = lift Ctx.new

hasType :: (STEff s r, Member (Reader (Ctx s)) r) => Name -> Type -> Eff r ()
hasType name t = do ctx <- ask
                    lift (Ctx.insert ctx name t)

lookupType :: forall s r . (STEff s r, Member (Reader (Ctx s)) r) => Name -> Eff r Type
lookupType name = do ctx :: Ctx s <- ask
                     ot <- lift (Ctx.lookup ctx name)
                     case ot of
                         Just t -> pure t
                         Nothing -> error $ "unbound " <> show name

-- BlockBuilder for pushing statements in

type BlockBuilder s = STRef s [Stmt]

emptyBlockBuilder :: STEff s r => Eff r (BlockBuilder s)
emptyBlockBuilder = lift (newSTRef [])

pushStmt :: (STEff s r, Member (Reader (BlockBuilder s)) r) => Stmt -> Eff r ()
pushStmt stmt = do builder :: BlockBuilder s <- ask
                   lift $ modifySTRef builder (stmt :)

buildBlock :: STEff s r => BlockBuilder s -> Transfer -> Eff r Block
buildBlock builder transfer = do stmts <- reverse <$> lift (readSTRef builder)
                                 pure $ Block stmts transfer

-- Continuation for continuing conversion

data Cont r = ContFn (Maybe Name) Type (Atom -> Eff r Transfer)
            | TrivCont Name

contParamHint :: Cont r -> Maybe (Name, Type)
contParamHint = \case ContFn nameHint t _ -> (, t) <$> nameHint
                      TrivCont _ -> Nothing

-- CPS Convert program

type ConvEffs s r = ( Member (State Int) r
                    , Member (Reader (Ctx s)) r
                    , Member (Reader (BlockBuilder s)) r
                    , SetMember Lift (Lift (ST s)) r )

cpsConvert :: (STEff s r, Member (State Int) r) => TypedExpr -> Eff r Expr
cpsConvert expr = do ctx <- emptyCtx
                     builder <- emptyBlockBuilder
                     runReader builder (runReader ctx m)
    where m = do builder <- ask
                 halt <- gensym (convert @Text "halt")
                 transfer <- doConvert (TrivCont halt) expr
                 body <- buildBlock builder transfer
                 pure $ Fn [(halt, FnType [int])] body

-- Implementation of CPS conversion

convertToBlock :: ConvEffs s r => Cont r -> TypedExpr -> Eff r Block
convertToBlock cont expr = do builder <- emptyBlockBuilder
                              transfer <- local (const builder)
                                                (doConvert cont expr)
                              buildBlock builder transfer

doConvert :: ConvEffs s r => Cont r -> TypedExpr -> Eff r Transfer
doConvert cont = \case
    Ast.Lambda parameters body ->
        do let params = fmap (second convert) parameters
           traverse_ (\(name, t) -> hasType name t) params
           ret <- gensym (convert @Text "r")
           codomain <- typeOf body
           hasType ret codomain
           body' <- convertToBlock (TrivCont ret) body
           continue cont $ Fn ((ret, FnType [codomain]) : params) body'
    Ast.App callee args ->
        do ret <- nominalizeCont cont
           calleeType <- typeOf callee
           let cont' = ContFn Nothing calleeType $ \aCallee ->
                   do nCallee <- nominalize Nothing (Atom aCallee)
                      let k = \aArgs -> pure $ App nCallee (Use ret : aArgs)
                      doConvertArgs k args
           doConvert cont' callee
    Ast.PrimApp op args ->
        let k = \aArgs -> continue cont (PrimApp op aArgs)
        in doConvertArgs k args
    Ast.Let (Ast.Val name (Ast.MonoType t) expr : decls) body ->
        let t' = convert t
            cont' = ContFn (Just name) t' $ \_ ->
                doConvert cont $ Ast.Let decls body
        in doConvert cont' expr
    Ast.Let [] body -> doConvert cont body
    Ast.If cond conseq alt ->
        do k <- TrivCont <$> nominalizeCont cont
           let cont' = ContFn Nothing bool $ \aCond ->
                   If aCond <$> convertToBlock k conseq <*> convertToBlock k alt
           doConvert cont' cond
    Ast.Var name -> continue cont (Atom (Use name))
    Ast.Const c -> continue cont (Atom (Const c))

doConvertArgs :: ConvEffs s r => ([Atom] -> Eff r Transfer) -> [TypedExpr] -> Eff r Transfer
doConvertArgs cont arguments = loop arguments []
    where loop [] aArgs = cont (reverse aArgs)
          loop (arg : args) aArgs = do argType <- typeOf arg
                                       let cont' = ContFn Nothing argType $ \aArg ->
                                               loop args (aArg : aArgs)
                                       doConvert cont' arg

continue :: ConvEffs s r => Cont r -> Expr -> Eff r Transfer
continue cont expr = do aExpr <- trivialize (contParamHint cont) expr
                        case cont of
                            ContFn _ _ k -> k aExpr
                            TrivCont k -> pure (App k [aExpr])

-- Reducing Expr:s to Atoms of Names

trivialize :: ConvEffs s r => Maybe (Name, Type) -> Expr -> Eff r Atom
trivialize (Just hint) expr = Use <$> nominalize (Just hint) expr
trivialize Nothing expr = case expr of
    Atom a -> pure a
    _ -> Use <$> nominalize Nothing expr

nominalize :: ConvEffs s r => Maybe (Name, Type) -> Expr -> Eff r Name
nominalize (Just (name, t)) expr = do pushStmt $ Def name t expr
                                      hasType name t
                                      pure name
nominalize Nothing expr = case expr of
    Atom (Use name) -> pure name
    _ -> do name <- gensym (convert @Text "v")
            t <- typeOf expr
            nominalize (Just (name, t)) expr

nominalizeCont :: ConvEffs s r => Cont r -> Eff r Name
nominalizeCont = \case ContFn paramHint paramType k ->
                           do param <- case paramHint of
                                           Just param -> pure param
                                           Nothing -> gensym (convert @Text "x")
                              hasType param paramType
                              builder <- emptyBlockBuilder
                              transfer <- local (const builder)
                                                (k (Use param))
                              body <- buildBlock builder transfer
                              nominalize Nothing (Fn [(param, paramType)] body)
                       TrivCont k -> pure k

-- Type inference

class CPSTypable s a where
    typeOf :: (STEff s r, Member (Reader (Ctx s)) r) => a -> Eff r Type

instance CPSTypable s Expr where
    typeOf = \case Fn params _ -> pure $ FnType (fmap snd params)
                   PrimApp op _ -> pure (primopResType op)
                   Atom a -> typeOf a

instance CPSTypable s Atom where
    typeOf = \case Use name -> lookupType name
                   Const c -> typeOf c

instance CPSTypable s Const where
    typeOf = \case IntConst _ -> pure $ TypeName (convert @Text "Int")

-- OPTIMIZE
instance CPSTypable s TypedExpr where
    typeOf = \case
        Ast.Lambda [(_, domain)] body ->
            do codomain <- typeOf body
               pure (FnType [FnType [codomain], convert domain])
        Ast.App callee _ -> typeOf callee >>= \case
            FnType (FnType [codomain] : _) -> pure codomain
            _ -> error "unreachable"
        Ast.PrimApp op _ -> pure (primopResType op)
        Ast.Let _ body -> typeOf body
        Ast.If _ conseq _ -> typeOf conseq
        Ast.Var name -> lookupType name
        Ast.Const (IntConst _) -> pure int
