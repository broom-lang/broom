module Ast ( Expr(..), Decl(..), Primop(..), Const(..), Type(..), PrimType(..)
           , primopResType ) where

import Data.Data (Data, Typeable)

import Data.Semigroup ((<>))
import Data.Convertible (Convertible, convert)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc ( Pretty, pretty, (<+>), line, hsep, vsep, parens
                                 , align, indent)

import Util (Name)

data Expr m t = Lambda [(Name, m)] (Expr m t)
              | App (Expr m t) [Expr m t]
              | PrimApp Primop [Expr m t]
              | Let [Decl m t] (Expr m t)
              | If (Expr m t) (Expr m t) (Expr m t)
              | Var Name
              | Const Const
              deriving (Data, Typeable)

data Decl m t = Val Name t (Expr m t)
              | Expr (Expr m t)
              deriving (Data, Typeable)

data Primop = VarNew | VarInit | VarLoad | Eq | Add | Sub | Mul | Div
            deriving (Show, Data, Typeable)

data Const = IntConst Int
           | UnitConst
           deriving (Data, Typeable)

data Type = TypeForAll Name Type
          | TypeArrow Type Type
          | TypeName Name
          | PrimType PrimType
          deriving (Eq, Data, Typeable)

data PrimType = TypeInt
              | TypeBool
              | TypeUnit
              deriving (Eq, Data, Typeable)

primopResType :: Primop -> Type
primopResType = PrimType . \case
    Add -> TypeInt
    Sub -> TypeInt
    Mul -> TypeInt
    Div -> TypeInt
    Eq -> TypeBool

instance (Pretty m, Pretty t) => Pretty (Expr m t) where
    pretty (Lambda params body) =
        "fn" <+> hsep (fmap prettyParam params) <+> "=>" <+> pretty body
        where prettyParam (param, paramType) = pretty param <> ":" <+> pretty paramType
    pretty (App callee args) = parens $ pretty callee <+> hsep (fmap pretty args)
    pretty (PrimApp op args) = parens $ pretty op <+> hsep (fmap pretty args)
    pretty (Let decls body) =
        "let" <+> align (vsep (fmap pretty decls)) <> line <> "in" <> line <>
            indent 4 (pretty body) <> line <> "end"
    pretty (If cond conseq alt) = align ("if" <+> pretty cond <> line <>
                                         "then" <+> pretty conseq <> line <>
                                         "else" <+> pretty alt)
    pretty (Var name) = pretty name
    pretty (Const c) = pretty c

instance (Pretty m, Pretty t) => Pretty (Decl m t) where
    pretty (Val pattern t valueExpr) =
        "val" <+> pretty pattern <> ":" <+> pretty t <+> "=" <+> pretty valueExpr
    pretty (Expr expr) = pretty expr

instance Pretty Primop where
    pretty op = "__" <> pretty (show op)

instance Pretty Const where
    pretty (IntConst n) = pretty n

instance Pretty Type where
    pretty (TypeForAll param t) =
        "forall" <+> pretty param <+> "." <+> pretty t
    pretty (TypeArrow domain codomain) = pretty domain <+> "->" <+> pretty codomain
    pretty (TypeName name) = pretty name
    pretty (PrimType p) = pretty p

instance Pretty PrimType where
    pretty TypeInt = "Int"
    pretty TypeBool = "Bool"
    pretty TypeUnit = "()"
