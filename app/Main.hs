module Main where

import Data.Text.Prettyprint.Doc (pretty)
import Data.Text.Prettyprint.Doc.Render.Text (putDoc)

import Lexer (alexScanTokens)
import Parser (parser)
import Typecheck (typecheck)
import Eval (eval, runEvaluation, emptyEnv)
import qualified JSBackend as JS

main :: IO ()
main = do src <- getContents
          let expr = parser (alexScanTokens src)
          print expr
          typecheck expr >>= \case Right (texpr, t) ->
                                       do putStrLn (show texpr ++ " : " ++ show t)
                                          ov <- runEvaluation $ eval emptyEnv texpr
                                          case ov of
                                              Right value -> print value
                                              Left err -> putStrLn ("EvalError: " ++ show err)
                                          let js = JS.selectInstructions texpr
                                          putDoc $ pretty js
                                   Left err -> putStrLn ("TypeError: " ++ show err)
