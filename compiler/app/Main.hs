{-# LANGUAGE DataKinds #-}

module Main where

import System.IO (stderr)
import qualified Data.Text.IO as TextIO
import Data.Semigroup ((<>))
import Data.Bifunctor (first)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc (Doc, Pretty, pretty, line, (<+>))
import Data.Text.Prettyprint.Doc.Render.Text (putDoc, hPutDoc)
import Control.Monad.ST.Strict (RealWorld, stToIO)
import Control.Eff (Eff, Member)
import Control.Eff.Lift (runLift)
import Control.Eff.State.Strict (State, evalState)
import Control.Eff.Exception (Exc, runError, liftEither)
import qualified Options.Applicative as Argv
import Options.Applicative ((<**>), switch, long, help, info, helper, fullDesc, header, progDesc)

import Language.Broom.Lexer (alexScanTokens)
import Language.Broom.Parser (parser)
import Language.Broom.Typecheck (TypeError, typecheck)
import qualified Language.Broom.Alphatize as Alphatize
import Language.Broom.Alphatize (alphatize)
import qualified Language.Broom.Linearize as Linearize
import Language.Broom.Linearize (linearize)
import Language.Broom.CPSConvert (STEff, cpsConvert)
import Language.Broom.MetaCont (threadMetaCont)
import qualified Language.Broom.JSBackend as JS
import Paths_broom (getDataFileName)

data CommandLine = CommandLine { dumpCst :: Bool
                               , dumpAst :: Bool
                               , dumpLinear :: Bool
                               , dumpCPS :: Bool }

optParser :: Argv.ParserInfo CommandLine
optParser = info (parseArgs <**> helper)
                 (fullDesc
                  <> header "Broom compiler"
                  <> progDesc "Compile Broom code from stdin")
    where parseArgs = CommandLine <$> switch (long "cst" <> help "Dump parse tree")
                                  <*> switch (long "ast" <> help "Dump (typechecked) AST")
                                  <*> switch (long "lin" <> help "Dump linearized AST")
                                  <*> switch (long "cps" <> help "Dump CPS IR")

data Err h = TypeError (TypeError h)
           | AlphaError Alphatize.Err
           | LinError Linearize.Err

instance Pretty (Err h) where
    pretty (TypeError err) = "TypeError:" <+> pretty err
    pretty (AlphaError err) = pretty err
    pretty (LinError err) = pretty err

compile :: forall s r ann . (STEff s r, Member (State Int) r, Member (Exc (Err s)) r)
                          => CommandLine -> Text -> String -> Eff r (Doc ann)
compile CommandLine { dumpCst, dumpAst, dumpLinear, dumpCPS } runtime src =
    let expr = parser (alexScanTokens src)
    in if dumpCst
       then pure (pretty expr)   
       else do typingRes <- typecheck expr
               texpr <- liftEither (first (TypeError :: TypeError s -> Err s) typingRes)
               if dumpAst
               then pure (pretty texpr)
               else do ares <- alphatize texpr
                       aexpr <- liftEither (first (AlphaError :: Alphatize.Err -> Err s) ares)
                       linRes <- linearize aexpr
                       lexpr <- liftEither (first (LinError :: Linearize.Err -> Err s) linRes)
                       if dumpLinear
                       then pure (pretty lexpr)
                       else do cps0 <- cpsConvert lexpr
                               cps <- threadMetaCont cps0
                               if dumpCPS
                               then pure (pretty cps)
                               else let js = JS.selectInstructions cps
                                    in pure (pretty runtime <> line <>
                                             pretty js)

main :: IO ()
main = do cline <- Argv.execParser optParser
          runtime <- TextIO.readFile =<< getDataFileName "../runtime/runtime.js"
          src <- getContents
          res <- stToIO $ runLift $ runError $ evalState (0 :: Int) (compile cline runtime src)
          case res of
              Left (err :: Err RealWorld) -> hPutDoc stderr (pretty err)
              Right doc -> putDoc doc
