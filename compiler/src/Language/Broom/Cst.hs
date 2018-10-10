module Language.Broom.Cst ( Expr(..), Stmt(..), Primop(..), Const(..), Type(..), PrimType(..)
           , primopResType ) where

import Data.Data (Data, Typeable)

import Data.Semigroup ((<>))
import Data.Text.Prettyprint.Doc ( Pretty, pretty, (<+>), line, hsep, vsep, parens
                                 , align, indent)

import Language.Broom.Util (Name)

data Expr = Lambda Name (Maybe Type) Expr
          | App Expr Expr
          | PrimApp Primop [Expr]
          | Let [Stmt] Expr
          | If Expr Expr Expr
          | IsA Expr Type
          | Var Name
          | Const Const
          deriving (Data, Typeable)

data Stmt = Val Name (Maybe Type) Expr
          | Expr Expr
          deriving (Data, Typeable)

data Primop = SafePoint | VarNew | VarInit | VarLoad | Eq | Add | Sub | Mul | Div
            deriving (Show, Data, Typeable)

data Const = IntConst Int
           | UnitConst
           deriving (Data, Typeable)

data Type = TypeForAll Name Type
          | TypeArrow Type Type
          | TypeApp Type Type
          | TypeName Name
          | PrimType PrimType
          deriving (Eq, Data, Typeable)

data PrimType = TypeInt
              | TypeBool
              | TypeUnit
              | VarBox
              | TypeMetaCont
              deriving (Eq, Data, Typeable)

primopResType :: Primop -> [Type] -> Type
primopResType op argTypes = case op of
    SafePoint -> PrimType TypeMetaCont
    VarNew -> case argTypes of
                  [argType] -> TypeApp (PrimType VarBox) argType
                  _ -> undefined
    VarInit -> PrimType TypeUnit
    VarLoad -> case argTypes of
                   [TypeApp (PrimType VarBox) contentType] -> contentType
                   _ -> error $ "tried a VarLoad from " <> show (pretty argTypes)
    Add -> PrimType TypeInt
    Sub -> PrimType TypeInt
    Mul -> PrimType TypeInt
    Div -> PrimType TypeInt
    Eq -> PrimType TypeBool

instance Pretty Expr where
    pretty (Lambda param paramType body) =
        "fn" <+> pretty param <> ":" <+> pretty paramType <+> "=>" <+> pretty body
    pretty (App callee arg) = parens $ pretty callee <+> pretty arg
    pretty (PrimApp op args) = parens $ pretty op <+> hsep (fmap pretty args)
    pretty (Let decls body) =
        "let" <+> align (vsep (fmap pretty decls)) <> line <> "in" <> line <>
            indent 4 (pretty body) <> line <> "end"
    pretty (If cond conseq alt) = align ("if" <+> pretty cond <> line <>
                                         "then" <+> pretty conseq <> line <>
                                         "else" <+> pretty alt)
    pretty (IsA expr t) = pretty expr <> ":" <+> pretty t
    pretty (Var name) = pretty name
    pretty (Const c) = pretty c

instance Pretty Stmt where
    pretty (Val pattern t valueExpr) =
        "val" <+> pretty pattern <> ":" <+> pretty t <+> "=" <+> pretty valueExpr
    pretty (Expr expr) = pretty expr

instance Pretty Primop where
    pretty op = "__" <> pretty (show op)

instance Pretty Const where
    pretty (IntConst n) = pretty n
    pretty UnitConst = "()"

instance Pretty Type where
    pretty (TypeForAll param t) =
        "forall" <+> pretty param <+> "." <+> pretty t
    pretty (TypeArrow domain codomain) = pretty domain <+> "->" <+> pretty codomain
    pretty (TypeApp t arg) = parens (pretty t <+> pretty arg)
    pretty (TypeName name) = pretty name
    pretty (PrimType p) = pretty p

instance Pretty PrimType where
    pretty TypeInt = "Int"
    pretty TypeBool = "Bool"
    pretty TypeUnit = "()"
    pretty VarBox = "__VarBox"
    pretty TypeMetaCont = "__MetaCont"
