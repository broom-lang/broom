{
module Lexer (Token(..), alexScanTokens) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-
  $white+ ;
  fn   { const TokFn }
  :    { const TokHasType }
  "->" { const TokArrow }
  =>   { const TokDArrow }
  let  { const TokLet }
  =    { const TokEq }
  in   { const TokIn }
  end  { const TokEnd }
  "("  { const TokLParen }
  ")"  { const TokRParen }
  "{"  { const TokLBrace }
  "}"  { const TokRBrace }
  ","  { const TokComma }
  "."  { const TokDot }
  $alpha [$alpha $digit \_ \']* { TokVar }
  $digit+ { TokInt . read }

{
data Token = TokFn
           | TokHasType
           | TokArrow
           | TokDArrow
           | TokLet
           | TokEq
           | TokIn
           | TokEnd
           | TokLParen
           | TokRParen
           | TokLBrace
           | TokRBrace
           | TokComma
           | TokDot
           | TokVar String
           | TokInt Int
           deriving (Eq, Show)
}
