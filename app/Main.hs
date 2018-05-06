module Main where

import Lexer (alexScanTokens)
import Parser (parser)
import Typecheck (typecheck)
import Eval (eval, emptyEnv)

main :: IO ()
main = do src <- getContents
          let expr = parser (alexScanTokens src)
          t <- typecheck expr
          putStrLn (show expr ++ " : " ++ show t)
          print (eval emptyEnv expr)
