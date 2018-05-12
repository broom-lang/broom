{
module Parser (parser) where
import Lexer (Token(..))
import Ast (Expr(..), Type(..), Atom(..), Const(..))
}

%name parser
%tokentype { Token }
%error { parseError }

%token
  data { TokData }
  '|'  { TokBar }
  fn   { TokFn }
  ':'  { TokHasType }
  '->' { TokArrow }
  "=>" { TokDArrow }
  let  { TokLet }
  '='  { TokEq }
  in   { TokIn }
  end  { TokEnd }
  case { TokCase }
  of   { TokOf }
  '('  { TokLParen }
  ')'  { TokRParen }
  '{'  { TokLBrace }
  '}'  { TokRBrace }
  ','  { TokComma }
  '.'  { TokDot }
  var  { TokVar $$ }
  int  { TokInt $$ }

%%

Expr : data var '=' Variants in Expr end { Data $2 $4 $6 }
     | fn var "=>" Expr { Lambda $2 () $4 }
     | Expr Expr    { App $1 $2 }
     | let var '=' Expr in Expr end { Let $2 () $4 $6 }
     | case Expr of Matches end { Case $2 $4 }
     | '(' Expr ')' { $2 }
     | '{' Fields '}' { Record $2 }
     | Expr '.' var { Select $1 $3 }
     | Atom         { Atom $1 }

Variants : var Type { [($1, $2)] }
         | var Type '|' Variants { ($1, $2) : $4 }

Matches : var var "=>" Expr             { [($1, $2, $4)] }
        | var var "=>" Expr '|' Matches { ($1, $2, $4) : $6 }

Fields : { [] }
       | NonEmptyFields { $1 }

NonEmptyFields : var '=' Expr                    { [($1, $3)] }
               | var '=' Expr ',' NonEmptyFields { ($1, $3) : $5 }

Atom : var   { Var $1 }
     | Const { Const $1 }

Const : int { ConstInt $1 }

Type : var { PrimType $1 }
     | Type '->' Type { TypeArrow $1 $3 }
     | '{' Row '}' { RecordType $2 }

Row : { [] }
    | NonEmptyRow { $1 }

NonEmptyRow : var ':' Type                 { [($1, $3)] }
            | var ':' Type ',' NonEmptyRow { ($1, $3) : $5 }

{
parseError :: [Token] -> a
parseError [] = error "ParseError: unexpected EOF"
parseError (tok:_) = error $ "ParseError: unexpected " ++ show tok
}
