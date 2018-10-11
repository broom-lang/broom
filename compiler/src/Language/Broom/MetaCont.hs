module Language.Broom.MetaCont (threadMetaCont) where

import Data.Convertible (convert)
import Data.Text (Text)
import Control.Eff (Eff, Member)
import Control.Eff.Reader.Lazy (Reader, runReader, local, ask)
import Control.Eff.State.Strict (State)

import Language.Broom.Util (Name, gensym)
import Language.Broom.Cst (TypeAtom(..), PrimType(..), Primop(..))
import Language.Broom.CPS ( Block(..), Stmt(..), Transfer(..), Expr(..), Atom(..), Type(..))

-- Thread the metacontinuation through, insert safepoints and self-inject fns/conts:
threadMetaCont :: Member (State Int) r => Expr -> Eff r Expr
threadMetaCont expr = do mk <- gensym (convert ("mk" :: Text))
                         runReader mk (doThreadMC expr)

class ThreadMC c where
    doThreadMC :: (Member (Reader Name) r, Member (State Int) r) => c -> Eff r c

instance ThreadMC Expr where
    doThreadMC = \case
        Fn params body -> do self <- gensym (convert ("self" :: Text))
                             mk0 <- gensym (convert ("mk" :: Text))
                             mk <- gensym (convert ("mk" :: Text))
                             Block stmts transfer <- local (const mk) (doThreadMC body)
                             -- HACK: self type is self referential :S
                             let params' = (self, FnType $ fmap snd params')
                                           : (mk0, TAtom $ PrimType TypeMetaCont)
                                           : params
                             let safePoint = Def mk (TAtom $ PrimType TypeMetaCont)
                                                 (PrimApp SafePoint (fmap (Use . fst) params'))
                             pure $ Fn params' (Block (safePoint : stmts) transfer)
        p @ (PrimApp _ _) -> pure p
        a @ (Atom _) -> pure a

instance ThreadMC Block where
    doThreadMC (Block stmts transfer) = Block <$> traverse doThreadMC stmts
                                              <*> doThreadMC transfer

instance ThreadMC Stmt where
    doThreadMC (Def name t expr) = Def name t <$> doThreadMC expr
    doThreadMC (Expr expr) = Expr <$> doThreadMC expr

instance ThreadMC Transfer where
    doThreadMC (App callee args) = do mk <- ask
                                      pure $ App callee (Use callee : Use mk : args)
    doThreadMC (If cond conseq alt) = If cond <$> doThreadMC conseq <*> doThreadMC alt
