module Language.Broom.CPS ( Block(..), Transfer(..), Stmt(..), Expr(..), Atom(..), Type(..)
                          , primopResType ) where

import Data.Semigroup ((<>))
import Data.Convertible (Convertible, safeConvert)
import Data.Text.Prettyprint.Doc ( Pretty, pretty, line, (<+>), hsep, vsep, indent
                                 , parens, braces )

import Language.Broom.Util (Name)
import qualified Language.Broom.Cst as Cst
import Language.Broom.Cst (Primop(..), Const(..))

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

data Type = TypeForAll Name Type
          | FnType [Type]
          | TypeApp Type Type
          | TypeName Name
          | PrimType Cst.PrimType

instance Convertible Cst.Type Type where
    safeConvert = \case
        Cst.TypeForAll param t -> TypeForAll param <$> safeConvert t
        Cst.TypeArrow domain codomain ->
            do domain' <- safeConvert domain
               codomain' <- safeConvert codomain
               pure $ FnType [FnType [codomain'], domain']
        Cst.TypeApp t arg -> TypeApp <$> safeConvert t <*> safeConvert arg
        Cst.TypeName name -> pure (TypeName name)
        Cst.PrimType p -> pure (PrimType p)

primopResType :: Primop -> [Type] -> Type
primopResType op argTypes = case op of
    SafePoint -> PrimType Cst.TypeMetaCont
    VarNew -> case argTypes of
                  [argType] -> TypeApp (PrimType Cst.VarBox) argType
                  _ -> undefined
    VarInit -> PrimType Cst.TypeUnit
    VarLoad -> case argTypes of
                   [TypeApp (PrimType Cst.VarBox) contentType] -> contentType
                   _ -> error $ "tried a VarLoad from " <> show (pretty argTypes)
    Add -> PrimType Cst.TypeInt
    Sub -> PrimType Cst.TypeInt
    Mul -> PrimType Cst.TypeInt
    Div -> PrimType Cst.TypeInt
    Eq -> PrimType Cst.TypeBool

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
    pretty = \case TypeForAll param t ->
                       "forall" <+> pretty param <+> "." <+> pretty t
                   FnType domains -> parens ("fn" <+> hsep (fmap pretty domains))
                   TypeApp t arg -> parens (pretty t <+> pretty arg)
                   TypeName name -> pretty name
                   PrimType p -> pretty p
