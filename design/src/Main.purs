module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)

import Record (get, insert)
import Prim.Row (class Lacks, class Cons)
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Exists (Exists, mkExists, runExists)

import Control.Monad.Reader as R

-- # Seq

data Seq k a r
    = EmptyS (a -> r)
    | PushSeg (Exists (SeqCons k a r))
    | PushCo (Exists (SeqCo k a r))

data SeqCons k a r c = SeqCons (k a c) (Seq k c r)
data SeqCo k a r c = SeqCo (a -> c) (Seq k c r)

appendSeq :: forall k a r r' . Seq k a r -> Seq k r r' -> Seq k a r' 
appendSeq (EmptyS coerce) seq' = PushCo (mkExists (SeqCo coerce seq'))
appendSeq (PushSeg seqCons) seq' = runExists doAppend seqCons
    where
    doAppend :: forall d . SeqCons k a r d -> Seq k a r'
    doAppend (SeqCons s seq) = PushSeg (mkExists (SeqCons s (appendSeq seq seq')))
appendSeq (PushCo seqCo) seq' = runExists doAppend seqCo
    where
    doAppend :: forall d . SeqCo k a r d -> Seq k a r'
    doAppend (SeqCo coerce seq) = PushCo (mkExists (SeqCo coerce (appendSeq seq seq')))

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

