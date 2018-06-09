{
module Lexer (Token(..), alexScanTokens) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-
  $white+ ;
  val  { const TokVal }
  data { const TokData }
  "|"  { const TokBar }
  fn   { const TokFn }
  :    { const TokHasType }
  "->" { const TokArrow }
  =>   { const TokDArrow }
  let  { const TokLet }
  rec  { const TokRec }
  if   { const TokIf }
  then { const TokThen }
  else { const TokElse }
  ==   { TokBinOp }
  "+"  { TokBinOp }
  "-"  { TokBinOp }
  "*"  { TokBinOp }
  "/"  { TokBinOp }
  =    { const TokEq }
  in   { const TokIn }
  end  { const TokEnd }
  case { const TokCase }
  of   { const TokOf }
  "("  { const TokLParen }
  ")"  { const TokRParen }
  "{"  { const TokLBrace }
  "}"  { const TokRBrace }
  ","  { const TokComma }
  "."  { const TokDot }
  $alpha [$alpha $digit \_ \']* { TokVar }
  $digit+ { TokInt . read }

{
data Token = TokVal
           | TokData
           | TokBar
           | TokFn
           | TokHasType
           | TokArrow
           | TokDArrow
           | TokLet
           | TokRec
           | TokIf
           | TokThen
           | TokElse
           | TokEq
           | TokIn
           | TokEnd
           | TokCase
           | TokOf
           | TokLParen
           | TokRParen
           | TokLBrace
           | TokRBrace
           | TokComma
           | TokDot
           | TokBinOp String
           | TokVar String
           | TokInt Int
           deriving (Eq, Show)
}
