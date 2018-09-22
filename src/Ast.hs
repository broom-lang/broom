module Ast (Expr(..), Decl(..), Primop(..), Const(..), Type(..), MonoType(..)) where

import Data.Semigroup ((<>))
import Data.Text.Prettyprint.Doc ( Pretty, pretty, (<+>), line, hsep, vsep, parens
                                 , align, indent)

import Util (Name)

data Expr t = Lambda Name t (Expr t)
            | App (Expr t) (Expr t)
            | PrimApp Primop [Expr t]
            | Let [Decl t] (Expr t)
            | If (Expr t) (Expr t) (Expr t)
            | Var Name
            | Const Const

data Decl t = Val Name t (Expr t)

data Primop = Eq | Add | Sub | Mul | Div
            deriving Show

data Const = IntConst Int

data Type = TypeForAll [Name] MonoType
          | MonoType MonoType

data MonoType = TypeArrow MonoType MonoType
              | TypeName Name

instance Pretty t => Pretty (Expr t) where
    pretty (Lambda param paramType body) =
        "fn" <+> pretty param <> ":" <+> pretty paramType <+> "=>" <+> pretty body
    pretty (App callee arg) = parens $ pretty callee <+> pretty arg
    pretty (PrimApp op args) = parens $ pretty op <+> hsep (fmap pretty args)
    pretty (Let decls body) =
        "let" <+> vsep (fmap pretty decls) <> line <> "in" <> line <>
            indent 4 (pretty body) <> line <> "end"
    pretty (If cond conseq alt) = align ("if" <+> pretty cond <> line <>
                                         "then" <+> pretty conseq <> line <>
                                         "else" <+> pretty alt)
    pretty (Var name) = pretty name
    pretty (Const c) = pretty c

instance Pretty t => Pretty (Decl t) where
    pretty (Val pattern t valueExpr) =
        "val" <+> pretty pattern <> ":" <+> pretty t <+> "=" <+> pretty valueExpr

instance Pretty Primop where
    pretty op = "__" <> pretty (show op)

instance Pretty Const where
    pretty (IntConst n) = pretty n

instance Pretty Type where
    pretty (TypeForAll params t) =
        "forall" <+> hsep (fmap pretty params) <+> "." <+> pretty t
    pretty (MonoType t) = pretty t

instance Pretty MonoType where
    pretty (TypeArrow domain codomain) = pretty domain <+> "->" <+> pretty codomain
    pretty (TypeName name) = pretty name
