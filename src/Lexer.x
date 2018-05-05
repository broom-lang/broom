{
module Lexer (Token(..), alexScanTokens) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-
  $white+ ;
  fn { const TokFn }
  => { const TokDArrow }
  "(" { const TokLParen }
  ")" { const TokRParen }
  $alpha [$alpha $digit \_ \']* { TokVar }
  $digit+ { TokInt . read }

{
data Token = TokFn
           | TokDArrow
           | TokLParen
           | TokRParen
           | TokVar String
           | TokInt Int
	       deriving (Eq, Show)
}
