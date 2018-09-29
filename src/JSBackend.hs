module JSBackend (JSExpr, selectInstructions) where

import Data.Semigroup ((<>))
import Data.Text.Prettyprint.Doc ( Pretty, pretty
                                 , (<+>), line, hsep, vsep, parens, braces, tupled, indent
                                 , comma, punctuate )

import Util (Name)
import qualified Ast
import Ast (Expr, Decl, Primop, Const)

data JSExpr = Function [Name] [JSStmt]
            | Call JSExpr [JSExpr]
            | BinApp Binop JSExpr JSExpr
            | If JSExpr JSExpr JSExpr
            | Ref Name
            | Const Const

data JSStmt = FwdDef [Name]
            | Def Name JSExpr
            | Assign Name JSExpr
            | Expr JSExpr
            | Return JSExpr

data Binop = Eq | Add | Sub | Mul | Div

selectInstructions :: Expr m t -> JSExpr
selectInstructions =
    \case Ast.Lambda [(param, _)] body -> Function [param] [Return (selectInstructions body)]
          Ast.App callee args -> Call (selectInstructions callee) (fmap selectInstructions args)
          Ast.PrimApp op [l, r] ->
              BinApp (convertOp op) (selectInstructions l) (selectInstructions r)
          Ast.Let decls body ->
              Call (Function [] (fwdDecls decls :
                                fmap selectDecl decls <>
                                [Return (selectInstructions body)]))
                   []
          Ast.If cond conseq alt -> If (selectInstructions cond)
                                       (selectInstructions conseq)
                                       (selectInstructions alt)
          Ast.Var name -> Ref name
          Ast.Const c -> Const c

fwdDecls :: [Decl m t] -> JSStmt
fwdDecls decls = FwdDef (fmap declName decls)
    where declName (Ast.Val name _ _) = name

selectDecl :: Decl m t -> JSStmt
selectDecl (Ast.Val name _ valueExpr) = Assign name (selectInstructions valueExpr)

convertOp :: Primop -> Binop
convertOp =
    \case Ast.Eq -> Eq
          Ast.Add -> Add
          Ast.Sub -> Sub
          Ast.Mul -> Mul
          Ast.Div -> Div

instance Pretty JSExpr where
    pretty (Function params stmts) =
        parens ("function" <+> tupled (fmap pretty params) <+>
                   braces (line <> indent 4 (vsep (fmap pretty stmts)) <> line))
    pretty (Call callee args) = pretty callee <> tupled (fmap pretty args)
    pretty (BinApp op l r) = pretty l <+> pretty op <+> pretty r
    pretty (If cond conseq alt) =
        pretty cond <+> "?" <+> pretty conseq <+> ":" <+> pretty alt
    pretty (Ref name) = pretty name
    pretty (Const (Ast.IntConst n)) = pretty n

instance Pretty JSStmt where
    pretty (FwdDef names) = "var" <+> hsep (punctuate comma (fmap pretty names)) <> ";"
    pretty (Def name expr) = "var" <+> pretty name <+> "=" <+> pretty expr <> ";"
    pretty (Assign name expr) = pretty name <+> "=" <+> pretty expr <> ";"
    pretty (Expr expr) = pretty expr <> ";"
    pretty (Return expr) = "return" <+> pretty expr <> ";"

instance Pretty Binop where
    pretty = \case Eq -> "==="
                   Add -> "+"
                   Sub -> "-"
                   Mul -> "*"
                   Div -> "/"
