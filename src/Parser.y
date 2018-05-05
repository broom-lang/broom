{
module Parser (parser) where
import Lexer (Token(..))
import Ast (Expr(..), Atom(..), Const(..))
}

%name parser
%tokentype { Token }
%error { parseError }

%token
  fn   { TokFn }
  "=>" { TokDArrow }
  '('  { TokLParen }
  ')'  { TokRParen }
  var  { TokVar $$ }
  int  { TokInt $$ }

%%

Expr : fn var "=>" Expr { Lambda $2 $4 }
     | Expr Expr        { App $1 $2 }
     | '(' Expr ')'     { $2 }
     | Atom             { Atom $1 }

Atom : var   { Var $1 }
     | Const { Const $1 }

Const : int { ConstInt $1 }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"
}
