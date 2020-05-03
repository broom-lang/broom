module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)

import Record (get, insert)
import Prim.Row (class Lacks, class Cons)
import Data.Symbol (class IsSymbol, SProxy(..))

import Control.Monad.Reader as R

-- # Eff

-- TODO: StateT for "resource" state, ContT for callCC:
newtype Eff r a = Eff (R.ReaderT {| r} Effect a)

perform :: forall l e r' r rq . IsSymbol l => Cons l (rq -> e) r' r
    => SProxy l -> rq -> Eff r e
perform l req = Eff (R.asks (\handlers -> (get l handlers) req))

run :: forall a . Eff () a -> Effect a
run (Eff m) = R.runReaderT m {}

-- # Reader

ask :: forall r e . Eff (reader :: Unit -> e | r) e
ask = perform (SProxy :: SProxy "reader") unit

runReader :: forall r e a . Lacks "reader" r => Eff (reader :: Unit -> e | r) a -> e -> Eff r a
runReader (Eff m) env =
    Eff (R.withReaderT (\handlers -> insert (SProxy :: SProxy "reader") (\_ -> env) handlers) m)

-- ---

main :: Effect Unit
main = do
  log "🍝"

