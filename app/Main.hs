module Main where

import Lexer (alexScanTokens)
import Parser (parser)
import Typecheck (typeOf, emptyCtx)
import Eval (eval, emptyEnv)

main :: IO ()
main = do src <- getContents
          let expr = parser (alexScanTokens src)
          putStrLn (show expr ++ " : " ++ show (typeOf emptyCtx expr))
          print (eval emptyEnv expr)
