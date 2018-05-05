{
module Lexer (Token(..), alexScanTokens) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-

  $white+				;
  "--".*				;
  let					{ \s -> Let }
  in					{ \s -> In }
  $digit+				{ \s -> TokInt (read s) }
  [\=\+\-\*\/\(\)]			{ \s -> Sym (head s) }
  $alpha [$alpha $digit \_ \']*		{ \s -> Var s }

{
data Token =
	Let 		|
	In  		|
	Sym Char	|
	Var String	|
	TokInt Int
	deriving (Eq,Show)
}
