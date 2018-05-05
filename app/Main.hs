module Main where

import Lexer (alexScanTokens)
import Parser (parser)
import Eval (eval, emptyEnv)

main :: IO ()
main = do src <- getContents
          let expr = parser (alexScanTokens src)
          print expr
          print (eval emptyEnv expr)
