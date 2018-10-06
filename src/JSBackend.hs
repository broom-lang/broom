module JSBackend (JSExpr, selectInstrs) where

import Data.Semigroup ((<>))
import Data.Text.Prettyprint.Doc ( Doc, Pretty, pretty
                                 , (<+>), line, hsep, vsep, parens, braces, tupled, indent
                                 , comma, punctuate )

import Util (Name)
import qualified Ast
import Ast (Primop, Const)
import qualified CPS

-- FIXME: Correct by construction / more like the CPS types

data JSExpr = Function [Name] [JSStmt]
            | Call JSExpr [JSExpr]
            | BinApp Binop JSExpr JSExpr
            | Ref Name
            | Const Const

data JSStmt = FwdDef [Name]
            | Def Name JSExpr
            | Assign Name JSExpr
            | Expr JSExpr
            | Return JSExpr
            | If JSExpr [JSStmt] [JSStmt]

data Binop = Eq | Add | Sub | Mul | Div

class ISel c j where
    selectInstrs :: c -> j

instance ISel CPS.Block [JSStmt] where
    selectInstrs (CPS.Block stmts transfer) =
        fmap selectInstrs stmts <> [selectInstrs transfer]

-- FIXME: Emit code that throws on unbound (and rebound?) vars
instance ISel CPS.Stmt JSStmt where
    selectInstrs = \case
        CPS.Def name _ (CPS.PrimApp Ast.VarNew []) -> FwdDef [name]
        CPS.Def name _ valExpr -> Def name (selectInstrs valExpr)
        CPS.Expr (CPS.PrimApp Ast.VarInit [CPS.Use name, valExpr]) ->
            Assign name (selectInstrs valExpr)
        CPS.Expr expr -> Expr (selectInstrs expr)

instance ISel CPS.Expr JSExpr where
    selectInstrs = \case
        CPS.Fn params body -> Function (fmap fst params) (selectInstrs body)
        CPS.PrimApp Ast.VarLoad [CPS.Use name] -> Ref name
        CPS.PrimApp op [l, r] -> BinApp (convertOp op) (selectInstrs l) (selectInstrs r)
        CPS.Atom a -> selectInstrs a

instance ISel CPS.Transfer JSStmt where
    selectInstrs = \case
        CPS.App callee args -> Return $ Call (Ref callee) (fmap selectInstrs args)
        CPS.If cond conseq alt ->
            If (selectInstrs cond) (selectInstrs conseq) (selectInstrs alt)

instance ISel CPS.Atom JSExpr where
    selectInstrs = \case CPS.Use name -> Ref name
                         CPS.Const c -> Const c

convertOp :: Primop -> Binop
convertOp =
    \case Ast.Eq -> Eq
          Ast.Add -> Add
          Ast.Sub -> Sub
          Ast.Mul -> Mul
          Ast.Div -> Div

instance Pretty JSExpr where
    pretty (Function params stmts) =
        parens ("function" <+> tupled (fmap pretty params) <+> prettyBlock stmts)
    pretty (Call callee args) = pretty callee <> tupled (fmap pretty args)
    pretty (BinApp op l r) = pretty l <+> pretty op <+> pretty r
    pretty (Ref name) = pretty name
    pretty (Const (Ast.IntConst n)) = pretty n
    pretty (Const Ast.UnitConst) = "undefined"

instance Pretty JSStmt where
    pretty (FwdDef names) = "var" <+> hsep (punctuate comma (fmap pretty names)) <> ";"
    pretty (Def name expr) = "var" <+> pretty name <+> "=" <+> pretty expr <> ";"
    pretty (Assign name expr) = pretty name <+> "=" <+> pretty expr <> ";"
    pretty (Expr expr) = pretty expr <> ";"
    pretty (Return expr) = "return" <+> pretty expr <> ";"
    pretty (If cond conseq alt) =
        "if" <+> parens (pretty cond) <+> prettyBlock conseq <+> "else" <+> prettyBlock alt

instance Pretty Binop where
    pretty = \case Eq -> "==="
                   Add -> "+"
                   Sub -> "-"
                   Mul -> "*"
                   Div -> "/"

-- TODO: Have an explicit JSBlock so that this can be an `instance Pretty`:
prettyBlock :: [JSStmt] -> Doc a
prettyBlock stmts = braces (line <> indent 4 (vsep (fmap pretty stmts)) <> line)
