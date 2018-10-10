module Language.Broom.Ast (Expr(..), Stmt(..)) where

import Data.Data (Data, Typeable)

import Data.Semigroup ((<>))
import Data.Text.Prettyprint.Doc ( Pretty, pretty, (<+>), line, hsep, vsep, parens
                                 , align, indent)

import Language.Broom.Util (Name)
import Language.Broom.Cst (Const, Primop, Type)

data Expr = Lambda Name Type Expr
          | App Expr Expr Type
          | PrimApp Primop [Expr] Type
          | Let [Stmt] Expr
          | If Expr Expr Expr Type
          | IsA Expr Type
          | Var Name
          | Const Const
          deriving (Data, Typeable)

data Stmt = Val Name Type Expr
          | Expr Expr
          deriving (Data, Typeable)

instance Pretty Expr where
    pretty (Lambda param paramType body) =
        "fn" <+> pretty param <> ":" <+> pretty paramType <+> "=>" <+> pretty body
    pretty (App callee arg _) = parens $ pretty callee <+> pretty arg
    pretty (PrimApp op args _) = parens $ pretty op <+> hsep (fmap pretty args)
    pretty (Let decls body) =
        "let" <+> align (vsep (fmap pretty decls)) <> line <> "in" <> line <>
            indent 4 (pretty body) <> line <> "end"
    pretty (If cond conseq alt _) = align ("if" <+> pretty cond <> line <>
                                           "then" <+> pretty conseq <> line <>
                                           "else" <+> pretty alt)
    pretty (IsA expr t) = pretty expr <> ":" <+> pretty t
    pretty (Var name) = pretty name
    pretty (Const c) = pretty c

instance Pretty Stmt where
    pretty (Val pattern t valueExpr) =
        "val" <+> pretty pattern <> ":" <+> pretty t <+> "=" <+> pretty valueExpr
    pretty (Expr expr) = pretty expr
