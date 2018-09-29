{
module Parser (parser) where

import Lexer (Token(..))
import Ast (Expr(..), Decl(..), Type(..), MonoType(..), Primop(..), Const(..))
}

%name parser
%tokentype { Token }
%error { parseError }

%token
  val  { TokVal }
  data { TokData }
  '|'  { TokBar }
  fn   { TokFn }
  ':'  { TokHasType }
  forall { TokForAll }
  '->' { TokArrow }
  "=>" { TokDArrow }
  let  { TokLet }
  rec  { TokRec }
  if   { TokIf }
  then { TokThen }
  else { TokElse }
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

Nestable : fn var "=>" Expr { Lambda [($2, Nothing)] $4 }
         | fn var ':' MonoType "=>" Expr { Lambda [($2, Just $4)] $6 }
         | let Declarations in Expr end { Let $2 $4 }
         | if Expr then Expr else Expr { If $2 $4 $6 }
         | '(' Expr ')' { $2 }
         | var   { Var $1 }
         | Const { Const $1 }

Declarations : Declaration Declarations { $1 : $2 }
             | Declaration { [$1] }

Declaration : val var '=' Expr { Val $2 Nothing $4 }
            | val var ':' Type '=' Expr { Val $2 (Just $4) $6 }

Equal : Equal '==' Sum { PrimApp Eq [$1, $3] }
      | Sum { $1 }

Sum : Sum '+' Product { PrimApp Add [$1, $3] }
    | Sum '-' Product { PrimApp Sub [$1, $3] }
    | Product { $1 }

Product : Product '*' App { PrimApp Mul [$1, $3] }
        | Product '/' App { PrimApp Div [$1, $3] }
        | App { $1 }

App : App Nestable      { App $1 [$2] }
    | Nestable { $1 }

Matches : var var "=>" Expr             { [($1, $2, $4)] }
        | var var "=>" Expr '|' Matches { ($1, $2, $4) : $6 }

Fields : { [] }
       | NonEmptyFields { $1 }

NonEmptyFields : var '=' Expr                    { [($1, $3)] }
               | var '=' Expr ',' NonEmptyFields { ($1, $3) : $5 }

Const : int { IntConst $1 }

Type : forall var '.' MonoType { TypeForAll [$2] $4 }
     | MonoType                { MonoType $1 }

MonoType : MonoType '->' MonoType { TypeArrow $1 $3 }
         | var { TypeName $1 }

{
parseError :: [Token] -> a
parseError [] = error "ParseError: unexpected EOF"
parseError (tok:_) = error $ "ParseError: unexpected " ++ show tok
}
