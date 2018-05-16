{
module Parser (parser) where
import Lexer (Token(..))
import Ast (Expr(..), Type(..), Atom(..), Const(..))
import qualified Primop
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
  '==' { TokBinOp "==" }
  '+'  { TokBinOp "+" }
  '-'  { TokBinOp "-" }
  '*'  { TokBinOp "*" }
  '/'  { TokBinOp "/" }
  var  { TokVar $$ }
  int  { TokInt $$ }

%%

Expr : Nestable { $1 }
     | Equal { $1 }

Nestable : data var '=' Variants in Expr end { Data $2 $4 $6 }
         | fn var "=>" Expr { Lambda $2 () $4 }
         | let var '=' Expr in Expr end { Let $2 () $4 $6 }
         | case Expr of Matches end { Case $2 $4 }
         | '(' Expr ')' { $2 }
         | '{' Fields '}' { Record $2 }
         | Nestable '.' var { Select $1 $3 }
         | Atom         { Atom $1 }

Variants : var Type { [($1, $2)] }
         | var Type '|' Variants { ($1, $2) : $4 }

Equal : Equal '==' Sum { PrimApp Primop.Eq $1 $3 }
      | Sum { $1 }

Sum : Sum '+' Product { PrimApp Primop.Add $1 $3 }
    | Sum '-' Product { PrimApp Primop.Sub $1 $3 }
    | Product { $1 }

Product : Product '*' App { PrimApp Primop.Mul $1 $3 }
        | Product '/' App { PrimApp Primop.Div $1 $3 }
        | App { $1 }

App : App Nestable      { App $1 $2 }
    | Nestable { $1 }

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
