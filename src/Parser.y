{
module Parser (parser) where
import Lexer (Token(..))
import Ast (Expr(..), Const(..))
}

%name parser
%tokentype { Token }
%error { parseError }

%token
  int { TokInt $$ }

%%

Expr : int { Const (Int $1) }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"
}
