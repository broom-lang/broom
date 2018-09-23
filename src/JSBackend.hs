module JSBackend (JSExpr, selectInstructions) where

import Data.Semigroup ((<>))
import Data.Text.Prettyprint.Doc ( Pretty, pretty
                                 , (<+>), line, vsep, parens, braces, tupled, indent)

import Util (Name)
import qualified Ast
import Ast (Expr, Const)

data JSExpr = Function [Name] [JSStmt]
            | Call JSExpr [JSExpr]
            | Ref Name
            | Const Const

data JSStmt = Def Name JSExpr
            | Expr JSExpr
            | Return JSExpr

selectInstructions :: Expr m t -> JSExpr
selectInstructions =
    \case Ast.Lambda param _ body -> Function [param] [Return (selectInstructions body)]
          Ast.App callee arg -> Call (selectInstructions callee) [selectInstructions arg]
          Ast.Var name -> Ref name
          Ast.Const c -> Const c

instance Pretty JSExpr where
    pretty (Function params stmts) =
        parens ("function" <+> tupled (fmap pretty params) <+>
                   braces (line <> indent 4 (vsep (fmap pretty stmts)) <> line))
    pretty (Call callee args) = pretty callee <> tupled (fmap pretty args)
    pretty (Ref name) = pretty name
    pretty (Const (Ast.IntConst n)) = pretty n

instance Pretty JSStmt where
    pretty (Def name expr) = "var" <+> pretty name <+> "=" <+> pretty expr <> ";"
    pretty (Expr expr) = pretty expr <> ";"
    pretty (Return expr) = "return" <+> pretty expr <> ";"
