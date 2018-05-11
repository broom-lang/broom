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
  let  { TokLet }
  '='  { TokEq }
  in   { TokIn }
  end  { TokEnd }
  '('  { TokLParen }
  ')'  { TokRParen }
  '{'  { TokLBrace }
  '}'  { TokRBrace }
  ','  { TokComma }
  '.'  { TokDot }
  var  { TokVar $$ }
  int  { TokInt $$ }

%%

Expr : fn var "=>" Expr { Lambda $2 () $4 }
     | Expr Expr    { App $1 $2 }
     | let var '=' Expr in Expr end { Let $2 () $4 $6 }
     | '(' Expr ')' { $2 }
     | '{' Fields '}' { Record $2 }
     | Expr '.' var { Select $1 $3 }
     | Atom         { Atom $1 }

Fields : { [] }
       | NonEmptyFields { $1 }

NonEmptyFields : var '=' Expr                    { [($1, $3)] }
               | var '=' Expr ',' NonEmptyFields { ($1, $3) : $5 }

Atom : var   { Var $1 }
     | Const { Const $1 }

Const : int { ConstInt $1 }

{
parseError :: [Token] -> a
parseError [] = error "ParseError: unexpected EOF"
parseError (tok:_) = error $ "ParseError: unexpected " ++ show tok
}
