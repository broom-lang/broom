module Language.Broom.CPS ( Block(..), Transfer(..), Stmt(..), Expr(..), Atom(..), Type(..)
                          , primopResType ) where

import Data.Semigroup ((<>))
import Data.Convertible (Convertible, safeConvert)
import Data.Text.Prettyprint.Doc ( Pretty, pretty, line, (<+>), hsep, vsep, indent
                                 , parens, braces )

import Language.Broom.Util (Name)
import qualified Language.Broom.Cst as Cst
import Language.Broom.Cst (Primop(..), Const(..))

data Block h = Block [Stmt h] (Transfer h)

data Transfer h = App Name [Atom]
                | If Atom (Block h) (Block h)

data Stmt h = Def Name (Type h) (Expr h)
            | Expr (Expr h)

data Expr h = Fn [(Name, Type h)] (Block h)
            | PrimApp Primop [Atom]
            | Atom Atom

data Atom = Use Name
          | Const Const

data Type h = TypeForAll Name (Type h)
            | FnType [Type h]
            | TypeApp (Type h) (Type h)
            | TAtom (Cst.TypeAtom h)

instance Convertible (Cst.Type h) (Type h) where
    safeConvert = \case
        Cst.TypeForAll param t -> TypeForAll param <$> safeConvert t
        Cst.TypeArrow domain codomain ->
            do domain' <- safeConvert domain
               codomain' <- safeConvert codomain
               pure $ FnType [FnType [codomain'], domain']
        Cst.TypeApp t arg -> TypeApp <$> safeConvert t <*> safeConvert arg
        Cst.TAtom a -> pure (TAtom a)

primopResType :: Primop -> [Type h] -> Type h
primopResType op argTypes = case op of
    SafePoint -> TAtom $ Cst.PrimType Cst.TypeMetaCont
    VarNew -> case argTypes of
                  [argType] -> TypeApp (TAtom $ Cst.PrimType Cst.VarBox) argType
                  _ -> undefined
    VarInit -> TAtom $ Cst.PrimType Cst.TypeUnit
    VarLoad -> case argTypes of
                   [TypeApp (TAtom (Cst.PrimType Cst.VarBox)) contentType] -> contentType
                   _ -> error $ "tried a VarLoad from " <> show (pretty argTypes)
    Add -> TAtom $ Cst.PrimType Cst.TypeInt
    Sub -> TAtom $ Cst.PrimType Cst.TypeInt
    Mul -> TAtom $ Cst.PrimType Cst.TypeInt
    Div -> TAtom $ Cst.PrimType Cst.TypeInt
    Eq -> TAtom $ Cst.PrimType Cst.TypeBool

instance Pretty (Block h) where
    pretty (Block stmts transfer) =
        let prettyStmts = fmap (\stmt -> pretty stmt <> ";") stmts
        in braces (line <> indent 4 (vsep (prettyStmts <> [pretty transfer])) <> line)

instance Pretty (Stmt h) where
    pretty = \case Def name t expr ->
                       pretty name <> ":" <+> pretty t <+> "=" <+> pretty expr
                   Expr expr -> pretty expr

instance Pretty (Transfer h) where
    pretty = \case App dest args -> pretty dest <+> hsep (fmap pretty args)
                   If cond dest alt ->
                       "if" <+> pretty cond <+> pretty dest <+> pretty alt

instance Pretty (Expr h) where
    pretty = \case Fn params body ->
                       "fn" <+> hsep (fmap prettyParam params) <+>
                           pretty body
                       where prettyParam (name, t) = pretty name <> ":" <+> pretty t
                   PrimApp op args -> pretty op <+> hsep (fmap pretty args)
                   Atom a -> pretty a

instance Pretty Atom where
    pretty (Use name) = pretty name
    pretty (Const c) = pretty c

instance Pretty (Type h) where
    pretty = \case TypeForAll param t ->
                       "forall" <+> pretty param <+> "." <+> pretty t
                   FnType domains -> parens ("fn" <+> hsep (fmap pretty domains))
                   TypeApp t arg -> parens (pretty t <+> pretty arg)
                   TAtom a -> pretty a
