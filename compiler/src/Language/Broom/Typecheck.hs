{-# LANGUAGE ConstraintKinds #-}

module Language.Broom.Typecheck (TypeError, Expr, Stmt, typecheck) where

import Data.Foldable (foldl')
import Data.Semigroup ((<>))
import Data.Convertible (convert)
import Data.Maybe (fromJust)
import qualified Data.HashMap.Lazy as HashMap
import Data.Text.Prettyprint.Doc (Pretty, pretty, (<+>))
import Control.Eff (Eff, Member, run)
import qualified Control.Eff.State.Strict as StrictState
import Control.Eff.State.Lazy (State, evalState, get, put, modify)
import Control.Eff.Exception (Exc, runError, throwError)

import Language.Broom.Util (Name, gensym, (<&>))
import qualified Language.Broom.Cst as Cst
import Language.Broom.Cst ( Const(..), Primop(..), Type(..), MonoType(..), TypeAtom(..)
                          , PrimType(..), constType, primopResType )
import Language.Broom.Ast (Expr(..), Stmt(..), Def(..))

data TypeError = Unbound Name
               | TypeMismatch Type Type
               | UnCallable Cst.Expr Type
               | Argc Int Int

instance Pretty TypeError where
    pretty (Unbound name) = "Unbound:" <+> pretty name
    pretty (TypeMismatch t u) =
        "TypeMismatch:" <+> "expected" <+> pretty t <> ", got" <+> pretty u
    pretty (UnCallable expr t) = "Uncallable:" <+> pretty expr <> ":" <+> pretty t
    pretty (Argc goal actual) =
        "Wrong number of arguments:" <+> "expected" <+> pretty goal <>
            ", got" <+> pretty actual

data CtxEntry = TVar Name
              | EVar Def
              | UVar Name (Maybe MonoType)
              | Delim Name

newtype Ctx = Ctx [CtxEntry]

builtinCtx :: Ctx
builtinCtx = Ctx []

ctxPush :: CtxEntry -> Ctx -> Ctx
ctxPush e (Ctx es) = Ctx (e : es)

ctxPushDef :: Def -> Ctx -> Ctx
ctxPushDef def = ctxPush (EVar def)

ctxPushTVar :: Name -> Ctx -> Ctx
ctxPushTVar name = ctxPush (TVar name)

ctxPushUName :: Name -> Ctx -> Ctx
ctxPushUName name = ctxPush (UVar name Nothing)

ctxPopEVar :: Name -> Ctx -> Maybe Ctx
ctxPopEVar name (Ctx entries) = Ctx <$> pop entries
    where pop [] = Nothing
          pop (EVar (Def n _) : es) | n == name = Just es
          pop (_ : es) = pop es

ctxLookup :: Name -> Ctx -> Maybe Def
ctxLookup name (Ctx entries) = find entries
    where find [] = Nothing
          find (EVar (def @ (Def name' _)) : _) | name' == name = Just def
          find (_ : es) = find es

substitute :: Ctx -> Type -> Type
substitute = undefined

type TypingEffs r = ( Member (State Ctx) r
                    , Member (StrictState.State Int) r
                    , Member (Exc TypeError) r )

typecheck :: Member (StrictState.State Int) r => Cst.Expr -> Eff r (Either TypeError Expr)
typecheck expr = (fst <$>) <$> runError (evalState builtinCtx (check expr))

check :: TypingEffs r => Cst.Expr -> Eff r (Expr, Type)
check = \case
    Cst.Lambda param Nothing body ->
        do domainName <- gensym "a"
           let domain = TAtom $ TypeUName $ domainName
           codomainName <- gensym "b"
           let codomain = TAtom $ TypeUName $ codomainName
           modify ( ctxPushUName domainName
                  . ctxPushUName codomainName
                  . ctxPushDef (Def param domain) )
           body' <- checkAs codomain body
           modify (fromJust . ctxPopEVar param)
           pure (body', TypeArrow domain codomain)
    Cst.App callee arg -> do (callee', calleeT) <- check callee
                             subst <- get
                             checkRedex (substitute subst calleeT) arg
    Cst.IsA expr t -> do {expr' <- checkAs t expr; pure (IsA expr' t, t) }
    Cst.Var name -> do ctx :: Ctx <- get
                       case ctxLookup name ctx of
                           Just (def @ (Def _ t)) -> pure (Var def, t)
                           Nothing -> throwError (Unbound name)
    Cst.Const c -> pure (Const c, convert (constType c))

checkRedex :: TypingEffs r => Type -> Cst.Expr -> Eff r (Expr, Type)
checkRedex = undefined

checkAs  :: TypingEffs r => Type -> Cst.Expr -> Eff r Expr
checkAs (TypeArrow domain codomain) (Cst.Lambda param Nothing body) =
    do modify (ctxPushDef (Def param domain))
       body' <- checkAs codomain body
       modify (fromJust . ctxPopEVar param)
       pure body'
checkAs t (Cst.Var name) = do ctx :: Ctx <- get
                              case ctxLookup name ctx of
                                  Just (def @ (Def _ t')) -> checkSub t' t *> pure (Var def)
                                  Nothing -> throwError (Unbound name)
checkAs t (Cst.Const c) = checkSub (convert (constType c)) t *> pure (Const c)

checkSub :: TypingEffs r => Type -> Type -> Eff r ()
checkSub = undefined
