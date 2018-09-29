module Main where

import System.IO (stderr)
import Data.Semigroup ((<>))
import Data.Text.Prettyprint.Doc (pretty)
import Data.Text.Prettyprint.Doc.Render.Text (putDoc, hPutDoc)
import Control.Eff.Lift (runLift, lift)
import Control.Eff.Fresh (runFresh')
import qualified Options.Applicative as Argv
import Options.Applicative ((<**>), switch, long, help, info, helper, fullDesc, header, progDesc)

import Lexer (alexScanTokens)
import Parser (parser)
import Typecheck (typecheck)
import Alphatize (alphatize)
import qualified CPS
import CPS (cpsConvert)
import qualified JSBackend as JS

data CommandLine = CommandLine { dumpCPS :: Bool }

optParser :: Argv.ParserInfo CommandLine
optParser = info (parseArgs <**> helper)
                 (fullDesc 
                  <> header "Mulled compiler"
                  <> progDesc "Compile Mulled code from stdin")
    where parseArgs = CommandLine <$> switch (long "cps" <> help "Dump CPS IR")

main :: IO ()
main = do CommandLine { dumpCPS } <- Argv.execParser optParser
          src <- getContents
          let expr = parser (alexScanTokens src)
          case typecheck expr of
              Left typeError -> hPutDoc stderr (pretty typeError)
              Right typedExpr ->
                 runLift $ flip runFresh' 0 $ do
                    alphatizedExpr <- alphatize typedExpr
                    cps :: CPS.Expr <- CPS.cpsConvert alphatizedExpr
                    if dumpCPS
                    then lift $ putDoc (pretty cps)
                    else let js = JS.selectInstructions alphatizedExpr
                         in lift $ putDoc (pretty js)
