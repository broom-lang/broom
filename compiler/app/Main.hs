module Main where

import System.IO (stderr)
import qualified Data.Text.IO as TextIO
import Data.Semigroup ((<>))
import Data.Text.Prettyprint.Doc (Doc, pretty, line)
import Data.Text.Prettyprint.Doc.Render.Text (putDoc, hPutDoc)
import Control.Monad.ST.Strict (runST)
import Control.Eff (Eff, Member)
import Control.Eff.Lift (runLift)
import Control.Eff.State.Strict (State, evalState)
import qualified Options.Applicative as Argv
import Options.Applicative ((<**>), switch, long, help, info, helper, fullDesc, header, progDesc)

import Language.Broom.Lexer (alexScanTokens)
import Language.Broom.Parser (parser)
import Language.Broom.Typecheck (typecheck)
import Language.Broom.Alphatize (alphatize)
import Language.Broom.Linearize (linearize)
import qualified Language.Broom.CPS as CPS
import Language.Broom.CPSConvert (STEff, cpsConvert)
import Language.Broom.MetaCont (threadMetaCont)
import qualified Language.Broom.JSBackend as JS
import Paths_broom (getDataFileName)

data CommandLine = CommandLine { dumpLinear :: Bool, dumpCPS :: Bool }

optParser :: Argv.ParserInfo CommandLine
optParser = info (parseArgs <**> helper)
                 (fullDesc
                  <> header "Broom compiler"
                  <> progDesc "Compile Broom code from stdin")
    where parseArgs = CommandLine <$> switch (long "lin" <> help "Dump linearized AST")
                                  <*> switch (long "cps" <> help "Dump CPS IR")

main :: IO ()
main = do CommandLine { dumpLinear, dumpCPS } <- Argv.execParser optParser
          runtime <- TextIO.readFile =<< getDataFileName "../runtime/runtime.js"
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
                                        if dumpLinear
                                        then pure $ Right $ pretty linear
                                        else do cps0 :: CPS.Expr <- cpsConvert linear
                                                cps <- threadMetaCont cps0
                                                if dumpCPS
                                                then pure $ Right $ pretty cps
                                                else let js = JS.selectInstructions cps
                                                     in pure $ Right (pretty runtime <> line
                                                                      <> pretty js)
                 in case runST $ runLift $ evalState (0 :: Int) m of
                        Left errDoc -> hPutDoc stderr errDoc
                        Right exprDoc -> putDoc exprDoc
