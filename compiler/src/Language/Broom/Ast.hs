module Language.Broom.Ast (Expr(..), Stmt(..), Def(..), defName) where

import Data.Data (Data, Typeable)

import Data.Semigroup ((<>))
import Data.Text.Prettyprint.Doc ( Pretty, pretty, (<+>), line, hsep, vsep, parens
                                 , align, indent)

import Language.Broom.Util (Name)
import Language.Broom.Cst (Const, Primop, Type)

data Expr = Lambda Def Expr
          | App Expr Expr Type
          | PrimApp Primop [Expr] Type
          | Let [Stmt] Expr
          | If Expr Expr Expr Type
          | IsA Expr Type
          | Var Def
          | Const Const
          deriving (Data, Typeable)

data Stmt = Val Def Expr
          | Expr Expr
          deriving (Data, Typeable)

data Def = Def Name Type
         deriving (Data, Typeable)

defName :: Def -> Name
defName (Def name _) = name

instance Pretty Expr where
    pretty (Lambda def body) = "fn" <+> pretty def <+> "=>" <+> pretty body
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
    pretty (Val def valueExpr) =
        "val" <+> pretty def <+> "=" <+> pretty valueExpr
    pretty (Expr expr) = pretty expr

instance Pretty Def where
    pretty (Def name t) = pretty name <> ":" <+> pretty t
