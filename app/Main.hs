module Main where

import Data.Text.Prettyprint.Doc (pretty)
import Data.Text.Prettyprint.Doc.Render.Text (putDoc)

import Lexer (alexScanTokens)
import Parser (parser)
import qualified JSBackend as JS

main :: IO ()
main = do src <- getContents
          let expr = parser (alexScanTokens src)
          let js = JS.selectInstructions expr
          putDoc (pretty js)
