module Main where

import Lexer (alexScanTokens)
import Parser (parser)
import Typecheck (typecheck)
import Eval (eval, emptyEnv)

main :: IO ()
main = do src <- getContents
          let expr = parser (alexScanTokens src)
          print expr
          typingRes <- typecheck expr
          case typingRes of
              Right (expr, t) -> do putStrLn (show expr ++ " : " ++ show t)
                                    print (eval emptyEnv expr)
              Left err -> putStrLn ("TypeError: " ++ show err)
