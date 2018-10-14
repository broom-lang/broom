module Language.Broom.Ast (Expr(..), Stmt(..), Def(..), defName) where

import Data.Semigroup ((<>))
import Data.Generics.Uniplate.Operations (Uniplate, uniplate, Biplate, biplate)
import Data.Generics.Uniplate.Direct (plate, (|-), (|*), (||*), (||+))
import Data.Text.Prettyprint.Doc ( Pretty, pretty, (<+>), line, hsep, vsep, parens
                                 , align, indent)

import Language.Broom.Util (Name)
import Language.Broom.Cst (Const, Primop, Type)

data Expr h = Lambda (Def h) (Expr h)
            | App (Expr h) (Expr h) (Type h)
            | PrimApp Primop [Expr h] (Type h)
            | Let [Stmt h] (Expr h)
            | If (Expr h) (Expr h) (Expr h) (Type h)
            | IsA (Expr h) (Type h)
            | Var (Def h)
            | Const Const

data Stmt h = Val (Def h) (Expr h)
            | Expr (Expr h)

data Def h = Def Name (Type h)

defName :: Def h -> Name
defName (Def name _) = name

instance Uniplate (Expr h) where
    uniplate (Lambda param body) = plate Lambda |- param |* body
    uniplate (App callee arg t) = plate App |* callee |* arg |- t
    uniplate (PrimApp op args t) = plate PrimApp |- op ||* args |- t
    uniplate (Let stmts body) = plate Let ||+ stmts |* body
    uniplate (If cond conseq alt t) = plate If |* cond |* conseq |* alt |- t
    uniplate (IsA expr t) = plate IsA |* expr |- t
    uniplate (Var def) = plate Var |- def
    uniplate (Const c) = plate Const |- c

instance Biplate (Stmt h) (Expr h) where
    biplate (Val def expr) = plate Val |- def |* expr
    biplate (Expr expr) = plate Expr |* expr

instance Pretty (Expr h) where
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

instance Pretty (Stmt h) where
    pretty (Val def valueExpr) =
        "val" <+> pretty def <+> "=" <+> pretty valueExpr
    pretty (Expr expr) = pretty expr

instance Pretty (Def h) where
    pretty (Def name t) = pretty name <> ":" <+> pretty t
