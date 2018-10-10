{
module Language.Broom.Parser (parser) where

import Language.Broom.Lexer (Token(..))
import Language.Broom.Cst (Expr(..), Stmt(..), Type(..), PrimType(..), Primop(..), Const(..))
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
     | Ascription { $1 }

Nestable : fn var "=>" Expr { Lambda $2 Nothing $4 }
         | fn var ':' Type "=>" Expr { Lambda $2 (Just $4) $6 }
         | let Stmtarations in Expr end { Let $2 $4 }
         | if Expr then Expr else Expr { If $2 $4 $6 }
         | '(' Expr ')' { $2 }
         | var   { Var $1 }
         | Const { Const $1 }

Stmtarations : Stmtaration Stmtarations { $1 : $2 }
             | Stmtaration { [$1] }

Stmtaration : val var '=' Expr { Val $2 Nothing $4 }
            | val var ':' Type '=' Expr { Val $2 (Just $4) $6 }

Ascription : Equal ':' Type { IsA $1 $3 }
           | Equal { $1 }

Equal : Equal '==' Sum { PrimApp Eq [$1, $3] }
      | Sum { $1 }

Sum : Sum '+' Product { PrimApp Add [$1, $3] }
    | Sum '-' Product { PrimApp Sub [$1, $3] }
    | Product { $1 }

Product : Product '*' App { PrimApp Mul [$1, $3] }
        | Product '/' App { PrimApp Div [$1, $3] }
        | App { $1 }

App : App Nestable      { App $1 $2 }
    | Nestable { $1 }

Matches : var var "=>" Expr             { [($1, $2, $4)] }
        | var var "=>" Expr '|' Matches { ($1, $2, $4) : $6 }

Fields : { [] }
       | NonEmptyFields { $1 }

NonEmptyFields : var '=' Expr                    { [($1, $3)] }
               | var '=' Expr ',' NonEmptyFields { ($1, $3) : $5 }

Const : int { IntConst $1 }

Type : forall var '.' Type { TypeForAll $2 $4 }
     | Type '->' Type { TypeArrow $1 $3 }
     | var { case show $1 of
                 "Int" -> PrimType TypeInt
                 "Bool" -> PrimType TypeBool
                 _ -> TypeName $1 }

{
parseError :: [Token] -> a
parseError [] = error "ParseError: unexpected EOF"
parseError (tok:_) = error $ "ParseError: unexpected " ++ show tok
}
