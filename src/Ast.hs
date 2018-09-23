module Ast (Expr(..), Decl(..), Primop(..), Const(..), Type(..), MonoType(..), typeCon) where

import Data.Semigroup ((<>))
import Data.Convertible (Convertible, convert)
import Data.Text.Prettyprint.Doc ( Pretty, pretty, (<+>), line, hsep, vsep, parens
                                 , align, indent)

import Util (Name)

data Expr m t = Lambda Name m (Expr m t)
              | App (Expr m t) (Expr m t)
              | PrimApp Primop [Expr m t]
              | Let [Decl m t] (Expr m t)
              | If (Expr m t) (Expr m t) (Expr m t)
              | Var Name
              | Const Const

data Decl m t = Val Name t (Expr m t)

data Primop = Eq | Add | Sub | Mul | Div
            deriving Show

data Const = IntConst Int

data Type = TypeForAll [Name] MonoType
          | MonoType MonoType
          deriving Eq

data MonoType = TypeArrow MonoType MonoType
              | TypeName Name
              deriving Eq

typeCon :: Convertible n Name => n -> MonoType
typeCon = TypeName . convert

instance (Pretty m, Pretty t) => Pretty (Expr m t) where
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

instance (Pretty m, Pretty t) => Pretty (Decl m t) where
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
