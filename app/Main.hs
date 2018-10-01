module Main where

import System.IO (stderr)
import Data.Semigroup ((<>))
import Data.Text.Prettyprint.Doc (Doc, pretty)
import Data.Text.Prettyprint.Doc.Render.Text (putDoc, hPutDoc)
import Control.Monad.ST.Strict (runST)
import Control.Eff (Eff, Member)
import Control.Eff.Lift (runLift)
import Control.Eff.State.Strict (State, evalState)
import qualified Options.Applicative as Argv
import Options.Applicative ((<**>), switch, long, help, info, helper, fullDesc, header, progDesc)

import Lexer (alexScanTokens)
import Parser (parser)
import Typecheck (typecheck)
import Alphatize (alphatize)
import Linearize (linearize)
import qualified CPS
import CPSConvert (STEff, cpsConvert)
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
                 let m :: (STEff s r, Member (State Int) r)
                       => Eff r (Either (Doc ann) (Doc ann))
                     m = alphatize typedExpr >>= \case
                             Left alphaErr -> pure $ Left $ pretty alphaErr
                             Right alphatizedExpr ->
                                 case linearize alphatizedExpr of
                                    Left err -> pure $ Left $ pretty err
                                    Right linear ->
                                        do cps :: CPS.Expr <- cpsConvert linear
                                           if dumpCPS
                                           then pure $ Right $ pretty cps
                                           else let js = JS.selectInstructions alphatizedExpr
                                                in pure $ Right $ pretty js
                 in case runST $ runLift $ evalState (0 :: Int) m of
                        Left errDoc -> hPutDoc stderr errDoc
                        Right exprDoc -> putDoc exprDoc
