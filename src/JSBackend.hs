module JSBackend (JSExpr, selectInstructions) where

import Data.Semigroup ((<>))
import Data.Text (Text, pack, intercalate)
import Data.Text.Prettyprint.Doc ( Pretty, pretty
                                 , (<+>), line, vsep, braces, tupled, indent)

import Util (Name, nameToText)
import qualified Ast
import Ast (Expr, Const)
import Type (ClosedType)

data JSExpr = Function [Name] [JSStmt]
            | Call JSExpr [JSExpr]
            | Const Const

data JSStmt = Def Name JSExpr
            | Expr JSExpr
            | Return JSExpr

selectInstructions :: Expr ClosedType -> JSExpr
selectInstructions =
    \case Ast.Lambda param _ body -> Function [param] [Return (selectInstructions body)]
          Ast.App callee arg -> Call (selectInstructions callee) [selectInstructions arg]
          Ast.Atom (Ast.Const c) -> Const c

instance Pretty JSExpr where
    pretty (Function params stmts) =
        "function" <+> tupled (fmap pretty params) <+>
            braces (line <> indent 4 (vsep (fmap pretty stmts)) <> line)
    pretty (Call callee args) = pretty callee <> tupled (fmap pretty args)
    pretty (Const (Ast.ConstInt n)) = pretty n

instance Pretty JSStmt where
    pretty (Def name expr) = "var" <+> pretty name <+> "=" <+> pretty expr <> ";"
    pretty (Expr expr) = pretty expr <> ";"
    pretty (Return expr) = "return" <+> pretty expr <> ";"
