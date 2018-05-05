module Main where

import Lexer (alexScanTokens)
import Parser (parser)

main :: IO ()
main = parser . alexScanTokens <$> getContents >>= print
