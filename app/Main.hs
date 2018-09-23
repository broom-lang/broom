module Main where

import System.IO (stderr)
import Data.Text.Prettyprint.Doc (pretty)
import Data.Text.Prettyprint.Doc.Render.Text (putDoc, hPutDoc)

import Lexer (alexScanTokens)
import Parser (parser)
import Typecheck (typecheck)
import qualified JSBackend as JS

main :: IO ()
main = do src <- getContents
          let expr = parser (alexScanTokens src)
          case typecheck expr of
              Left typeError -> hPutDoc stderr (pretty typeError)
              Right typedExpr -> let js = JS.selectInstructions typedExpr
                                 in putDoc (pretty js)
