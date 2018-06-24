{
module Parser (parser) where

import Lexer (Token(..))
import Ast (Expr(..), Decl(..), Type(..), MonoType(..), Atom(..), Const(..))
import qualified Primop
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

Nestable : fn var "=>" Expr { Lambda $2 Nothing $4 }
         | fn var ':' Type "=>" Expr { Lambda $2 (Just $4) $6 }
         | let Declarations in Expr end { Let $2 $4 }
         | case Expr of Matches end { Case $2 $4 }
         | if Expr then Expr else Expr { If $2 $4 $6 }
         | '(' Expr ')' { $2 }
         | '{' Fields '}' { Record $2 }
         | Nestable '.' var { Select $1 $3 }
         | Atom { Atom $1 }

Declarations : Declaration Declarations { $1 : $2 }
             | Declaration { [$1] }

Declaration : val var '=' Expr { Val $2 Nothing $4 }
            | val var ':' Type '=' Expr { Val $2 (Just $4) $6 }
            | data var '=' Variants { Data $2 $4 }

Variants : var MonoType              { [($1, $2)] }
         | var MonoType '|' Variants { ($1, $2) : $4 }

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

Type : MonoType { MonoType $1 }

MonoType : MonoType '->' MonoType { TypeArrow $1 $3 }
         | '{' Row '}' { RecordType $2 }
         | var { TypeName $1 }

Row : { [] }
    | NonEmptyRow { $1 }

NonEmptyRow : var ':' MonoType                 { [($1, $3)] }
            | var ':' MonoType ',' NonEmptyRow { ($1, $3) : $5 }

{
parseError :: [Token] -> a
parseError [] = error "ParseError: unexpected EOF"
parseError (tok:_) = error $ "ParseError: unexpected " ++ show tok
}
