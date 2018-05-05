{
module Parser (parser) where
import Lexer (Token(..))
import Ast (Expr(..), Type(..), Atom(..), Const(..))
}

%name parser
%tokentype { Token }
%error { parseError }

%token
  fn   { TokFn }
  ':'  { TokHasType }
  '->' { TokArrow }
  "=>" { TokDArrow }
  '('  { TokLParen }
  ')'  { TokRParen }
  var  { TokVar $$ }
  int  { TokInt $$ }

%%

Expr : fn var ':' Type "=>" Expr { Lambda $2 $4 $6 }
     | Expr Expr    { App $1 $2 }
     | '(' Expr ')' { $2 }
     | Atom         { Atom $1 }

Type : Type '->' Type { TypeArrow $1 $3 }
     | var            { PrimType $1 }

Atom : var   { Var $1 }
     | Const { Const $1 }

Const : int { ConstInt $1 }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"
}
