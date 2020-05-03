module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)

import Record (insert)
import Prim.Row (class Lacks)
import Data.Symbol (SProxy(..))

import Control.Monad.Reader as R

-- # Eff

-- TODO: StateT for "resource" state, ContT for callCC:
newtype Eff r a = Eff (R.ReaderT {| r} Effect a)

run :: forall a . Eff () a -> Effect a
run (Eff m) = R.runReaderT m {}

-- # Reader

ask :: forall r e . Eff (reader :: e | r) e
ask = Eff(R.asks _.reader)

runReader :: forall r e a . Lacks "reader" r => Eff (reader :: e | r) a -> e -> Eff r a
runReader (Eff m) env =
    Eff (R.withReaderT (\handlers -> insert (SProxy :: SProxy "reader") env handlers) m)

-- ---

main :: Effect Unit
main = do
  log "🍝"

