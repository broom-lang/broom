{-# LANGUAGE TypeApplications, ConstraintKinds #-}

module CPS (Block(..), Transfer(..), Stmt(..), Expr(..), Atom(..), cpsConvert) where

import Data.Semigroup ((<>))
import Data.Bifunctor (second)
import Data.Foldable (traverse_)
import Data.Maybe (fromJust)
import qualified Data.Convertible as Convertible
import Data.Convertible (safeConvert)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc ( Pretty, pretty, line, (<+>), hsep, vsep, indent
                                 , parens, braces )
import qualified Data.HashMap.Lazy as Ctx
import Control.Eff (Eff, Member)
import Control.Eff.Fresh (Fresh)
import Control.Eff.State.Lazy (State, evalState, get, put, modify)

import Util (Name, gensym)
import qualified Ast
import Ast (Primop(..), Const(..))
import Typecheck (TypedExpr)

data Block = Block [Stmt] Transfer

data Transfer = App Name [Atom]
              | If Atom Block Block

data Stmt = Def Name Type Expr
          | Expr Expr

data Expr = Fn [(Name, Type)] Block
          | PrimApp Primop [Atom]
          | Atom Atom

data Atom = Use Name
          | Const Const

data Type = FnType [Type]
          | TypeName Name

instance Convertible.Convertible Ast.MonoType Type where
    safeConvert = \case
        Ast.TypeArrow domain codomain ->
            do domain' <- safeConvert domain
               codomain' <- safeConvert codomain
               pure $ FnType [FnType [codomain'], domain']
        Ast.TypeName name -> pure (TypeName name)

type Ctx = Ctx.HashMap Name Ast.MonoType

lookupMonoType :: Member (State Ctx) r => Name -> Eff r Ast.MonoType
lookupMonoType name = do ctx :: Ctx <- get
                         pure $ fromJust (Ctx.lookup name ctx)

lookupType :: Member (State Ctx) r => Name -> Eff r Type
lookupType name = Convertible.convert <$> lookupMonoType name

int :: Type
int = TypeName (Convertible.convert @Text "Int")

bool :: Type
bool = TypeName (Convertible.convert @Text "Bool")

primopResMonoType :: Primop -> Ast.MonoType
primopResMonoType = \case Add -> Ast.int
                          Sub -> Ast.int
                          Mul -> Ast.int
                          Div -> Ast.int
                          Eq -> Ast.bool

primopResType :: Primop -> Type
primopResType = \case Add -> int
                      Sub -> int
                      Mul -> int
                      Div -> int
                      Eq -> bool

class CPSTypable a where
    typeOf :: Member (State Ctx) r => a -> Eff r Type

instance CPSTypable TypedExpr where
    typeOf expr = Convertible.convert <$> monoTypeOf expr

instance CPSTypable Expr where
    typeOf = \case Fn params _ -> pure $ FnType (fmap snd params)
                   PrimApp op _ -> pure (primopResType op)
                   Atom a -> typeOf a

instance CPSTypable Atom where
    typeOf = \case Use name -> lookupType name
                   Const c -> typeOf c

instance CPSTypable Const where
    typeOf = \case IntConst _ -> pure $ TypeName (Convertible.convert @Text "Int")

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
cpsConvert expr = evalState (evalState conv ([[]] :: BlockBuilders)) (Ctx.empty :: Ctx)
    where conv = do halt <- gensym (Convertible.convert @Text "halt")
                    Fn [(halt, FnType [int])] <$> convert (TrivCont halt) expr

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

class CPSConvertible a where
    convert :: ConversionEffs r => Cont r -> a -> Eff r Block

instance CPSConvertible TypedExpr where
    convert cont = \case
        Ast.Lambda params body ->
            do traverse_ (\(name, t) -> modify (Ctx.insert name t)) params
               ret <- gensym (Convertible.convert @Text "r")
               let params' = fmap (second Convertible.convert) params
               bodyType <- typeOf body
               pushBlock
               cpsBody <- convert (TrivCont ret) body
               continue cont $ Fn ((ret, FnType [bodyType]) : params') cpsBody
        Ast.App callee args ->
            do ret <- nominalizeCont cont
               calleeType <- typeOf callee
               let cont' = ContFn calleeType $ \cpsCallee ->
                                        do aCallee <- nominalize cpsCallee
                                           let k = \aArgs ->
                                                    popBlock $ App aCallee (Use ret : aArgs)
                                           convertArgs k args
               convert cont' callee
        Ast.PrimApp op args ->
            let k = \aArgs -> continue cont (PrimApp op aArgs)
            in convertArgs k args
        Ast.Let (Ast.Val name (Ast.MonoType t) expr : decls) body ->
            do modify (Ctx.insert name t)
               let t' = Convertible.convert t
                   cont' = ContFn t' $ \cpsExpr ->
                       do pushStmt $ Def name t' cpsExpr
                          convert cont $ Ast.Let decls body
               convert cont' expr
        Ast.Let [] body -> convert cont body
        Ast.If cond conseq alt ->
            do k <- TrivCont <$> nominalizeCont cont
               let cont' = ContFn bool $ \cpsCond ->
                       do aCond <- trivialize cpsCond
                          pushBlock
                          conseqBlock <- convert k conseq
                          pushBlock
                          altBlock <- convert k alt
                          popBlock $ If aCond conseqBlock altBlock
               convert cont' cond
        Ast.Var name -> continue cont (Atom (Use name))
        Ast.Const c -> continue cont (Atom (Const c))

convertArgs :: forall r . ConversionEffs r => ([Atom] -> Eff r Block) -> [TypedExpr]
                                           -> Eff r Block
convertArgs cont arguments = loop arguments []
    where loop [] aArgs = cont (reverse aArgs)
          loop (arg : args) aArgs =
              do argType <- typeOf arg
                 let cont' :: Cont r
                     cont' = ContFn argType $ \cpsArg ->
                         do aArg <- trivialize cpsArg
                            loop args (aArg : aArgs)
                 convert cont' arg

nominalize :: ConversionEffs r => Expr -> Eff r Name
nominalize = \case
    Atom (Use name) -> pure name
    expr -> do name <- gensym (Convertible.convert @Text "v")
               t <- typeOf expr
               pushStmt $ Def name t expr
               pure name

nominalizeCont :: ConversionEffs r => Cont r -> Eff r Name
nominalizeCont = \case ContFn paramType k ->
                           do param <- gensym (Convertible.convert @Text "x")
                              pushBlock
                              body <- k (Atom (Use param))
                              nominalize $ Fn [(param, paramType)] body
                       TrivCont k -> pure k

trivialize :: ConversionEffs r => Expr -> Eff r Atom
trivialize = \case Atom a -> pure a
                   expr -> Use <$> nominalize expr

instance Pretty Block where
    pretty (Block stmts transfer) =
        let prettyStmts = fmap (\stmt -> pretty stmt <> ";") stmts
        in braces (line <> indent 4 (vsep (prettyStmts <> [pretty transfer])) <> line)

instance Pretty Stmt where
    pretty = \case Def name t expr ->
                       pretty name <> ":" <+> pretty t <+> "=" <+> pretty expr
                   Expr expr -> pretty expr
                   
instance Pretty Transfer where
    pretty = \case App dest args -> pretty dest <+> hsep (fmap pretty args)
                   If cond dest alt ->
                       "if" <+> pretty cond <+> pretty dest <+> pretty alt

instance Pretty Expr where
    pretty = \case Fn params body ->
                       "fn" <+> hsep (fmap prettyParam params) <+>
                           pretty body
                       where prettyParam (name, t) = pretty name <> ":" <+> pretty t
                   PrimApp op args -> pretty op <+> hsep (fmap pretty args)
                   Atom a -> pretty a

instance Pretty Atom where
    pretty (Use name) = pretty name
    pretty (Const c) = pretty c

instance Pretty Type where
    pretty = \case FnType domains -> parens ("fn" <+> hsep (fmap pretty domains))
                   TypeName name -> pretty name
