module Language.Broom.JSBackend (JSExpr, selectInstructions) where

import Data.Semigroup ((<>))
import Data.Convertible (convert)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc ( Doc, Pretty, pretty
                                 , (<+>), line, hsep, vsep, parens, braces, tupled, indent
                                 , comma, punctuate )

import Language.Broom.Util (Name)
import qualified Language.Broom.Cst as Cst
import Language.Broom.Cst (Primop, Const)
import qualified Language.Broom.CPS as CPS

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
            | If JSExpr [JSStmt] [JSStmt]

data Binop = Eq | Add | Sub | Mul | Div

selectInstructions :: CPS.Expr h -> JSStmt
selectInstructions expr = -- Hardcoded wrapper that enabled node `require(...).main()`
    Assign (convert ("module.exports.main" :: Text))
           (Call (Ref (convert ("wean" :: Text))) [selectInstrs expr])

class ISel c j where
    selectInstrs :: c -> j

instance ISel (CPS.Block h) [JSStmt] where
    selectInstrs (CPS.Block stmts transfer) =
        fmap selectInstrs stmts <> [selectInstrs transfer]

-- FIXME: Emit code that throws on unbound (and rebound?) vars
instance ISel (CPS.Stmt h) JSStmt where
    selectInstrs = \case
        CPS.Def name _ (CPS.PrimApp Cst.VarNew []) -> FwdDef [name]
        CPS.Def name _ valExpr -> Def name (selectInstrs valExpr)
        CPS.Expr (CPS.PrimApp Cst.VarInit [CPS.Use name, valExpr]) ->
            Assign name (selectInstrs valExpr)
        CPS.Expr expr -> Expr (selectInstrs expr)

instance ISel (CPS.Expr h) JSExpr where
    selectInstrs = \case
        CPS.Fn params body -> Function (fmap fst params) (selectInstrs body)
        CPS.PrimApp Cst.SafePoint args -> Call (Ref (convert ("safePoint" :: Text)))
                                               (fmap selectInstrs args)
        CPS.PrimApp Cst.VarLoad [CPS.Use name] -> Ref name
        CPS.PrimApp op [l, r] -> BinApp (convertOp op) (selectInstrs l) (selectInstrs r)
        CPS.Atom a -> selectInstrs a

instance ISel (CPS.Transfer h) JSStmt where
    selectInstrs = \case
        CPS.App callee args -> Expr $ Call (Ref callee) (fmap selectInstrs args)
        CPS.If cond conseq alt ->
            If (selectInstrs cond) (selectInstrs conseq) (selectInstrs alt)

instance ISel CPS.Atom JSExpr where
    selectInstrs = \case CPS.Use name -> Ref name
                         CPS.Const c -> Const c

convertOp :: Primop -> Binop
convertOp =
    \case Cst.Eq -> Eq
          Cst.Add -> Add
          Cst.Sub -> Sub
          Cst.Mul -> Mul
          Cst.Div -> Div

instance Pretty JSExpr where
    pretty (Function params stmts) =
        parens ("function" <+> tupled (fmap pretty params) <+> prettyBlock stmts)
    pretty (Call callee args) = pretty callee <> tupled (fmap pretty args)
    pretty (BinApp op l r) = pretty l <+> pretty op <+> pretty r
    pretty (Ref name) = pretty name
    pretty (Const (Cst.IntConst n)) = pretty n
    pretty (Const Cst.UnitConst) = "undefined"

instance Pretty JSStmt where
    pretty (FwdDef names) = "var" <+> hsep (punctuate comma (fmap pretty names)) <> ";"
    pretty (Def name expr) = "var" <+> pretty name <+> "=" <+> pretty expr <> ";"
    pretty (Assign name expr) = pretty name <+> "=" <+> pretty expr <> ";"
    pretty (Expr expr) = pretty expr <> ";"
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
