module Main where

import Lexer (alexScanTokens)
import Parser (parser)
import Typecheck (typecheck)
-- import Eval (eval, runEvaluation, emptyEnv)

main :: IO ()
main = do src <- getContents
          let expr = parser (alexScanTokens src)
          print expr
          typingRes <- typecheck expr
          case typingRes of
              Right (texpr, t) ->
                  do putStrLn (show texpr ++ " : " ++ show t)
                     -- value <- runEvaluation $ eval emptyEnv expr
                     -- case value of
                     --     Right value -> print value
                     --     Left err -> putStrLn ("EvalError: " ++ show err)
              Left err -> putStrLn ("TypeError: " ++ show err)
