{-# LANGUAGE ConstraintKinds #-}

module Language.Broom.Typecheck (TypeError, Expr, Stmt, typecheck) where

import Data.Foldable (foldl')
import Data.Semigroup ((<>))
import Data.Convertible (safeConvert, convert)
import Data.Maybe (fromJust)
import Data.STRef (STRef, newSTRef, writeSTRef)
import qualified Data.HashMap.Lazy as HashMap
import Data.Text.Prettyprint.Doc (Pretty, pretty, (<+>))
import Control.Monad.ST (ST)
import Control.Eff (Eff, Member, run)
import Control.Eff.Lift (Lifted, lift)
import qualified Control.Eff.State.Strict as StrictState
import Control.Eff.State.Lazy (State, evalState, get, put, modify)
import Control.Eff.Exception (Exc, runError, throwError)

import Language.Broom.Util (Name, gensym, (<&>))
import qualified Language.Broom.Cst as Cst
import Language.Broom.Cst ( Const(..), Primop(..), Type(..), MonoType(..), TypeAtom(..)
                          , PrimType(..), constType, primopResType )
import Language.Broom.Ast (Expr(..), Stmt(..), Def(..))

type UVar h = STRef h (Maybe (MonoType h))

freshUV :: Lifted (ST h) r => Eff r (UVar h)
freshUV = lift (newSTRef Nothing)

data TypeError h = Unbound Name
                 | TypeMismatch (Type h) (Type h)
                 | UnCallable (Cst.Expr h) (Type h)
                 | Argc Int Int
                 | Occurs (UVar h) (Type h)

instance Pretty (TypeError h) where
    pretty (Unbound name) = "Unbound:" <+> pretty name
    pretty (TypeMismatch t u) =
        "TypeMismatch:" <+> "expected" <+> pretty t <> ", got" <+> pretty u
    pretty (UnCallable expr t) = "Uncallable:" <+> pretty expr <> ":" <+> pretty t
    pretty (Argc goal actual) =
        "Wrong number of arguments:" <+> "expected" <+> pretty goal <>
            ", got" <+> pretty actual

data CtxEntry h = TVar Name
                | EVar (Def h)
                | UVar (UVar h)
                | Delim Name

newtype Ctx h = Ctx [CtxEntry h]

builtinCtx :: Ctx h
builtinCtx = Ctx []

ctxPush :: CtxEntry h -> Ctx h -> Ctx h
ctxPush e (Ctx es) = Ctx (e : es)

ctxPushDef :: Def h -> Ctx h -> Ctx h
ctxPushDef def = ctxPush (EVar def)

ctxPushTVar :: Name -> Ctx h -> Ctx h
ctxPushTVar name = ctxPush (TVar name)

ctxPushUName :: UVar h -> Ctx h -> Ctx h
ctxPushUName uv = ctxPush (UVar uv)

ctxInitUName :: Lifted (ST h) r => UVar h -> MonoType h -> Ctx h -> Eff r (Maybe (Ctx h))
ctxInitUName uv t ctx @ (Ctx entries) = init entries
    where init [] = pure Nothing
          init (UVar uv' : es) | uv == uv' = lift (writeSTRef uv (Just t)) *> pure (Just ctx)
          init (_ : es) = init es

ctxPopEVar :: Name -> Ctx h -> Maybe (Ctx h)
ctxPopEVar name (Ctx entries) = Ctx <$> pop entries
    where pop [] = Nothing
          pop (EVar (Def n _) : es) | n == name = Just es
          pop (_ : es) = pop es

ctxLookup :: Name -> Ctx h -> Maybe (Def h)
ctxLookup name (Ctx entries) = find entries
    where find [] = Nothing
          find (EVar (def @ (Def name' _)) : _) | name' == name = Just def
          find (_ : es) = find es

type TypingEffs h r = ( Lifted (ST h) r
                      , Member (State (Ctx h)) r
                      , Member (StrictState.State Int) r
                      , Member (Exc (TypeError h)) r )

typecheck :: forall h r . (Lifted (ST h) r, Member (StrictState.State Int) r)
                        => Cst.Expr h -> Eff r (Either (TypeError h) (Expr h))
typecheck expr = (fst <$>) <$> runError (evalState (builtinCtx :: Ctx h) (check expr))

check :: forall h r . TypingEffs h r => Cst.Expr h -> Eff r (Expr h, Type h)
check = \case
    Cst.Lambda param Nothing body ->
        do domainUV <- freshUV
           let domain = TAtom $ TypeUName $ domainUV
           codomainUV <- freshUV
           let codomain = TAtom $ TypeUName $ codomainUV
           let def = Def param domain
           modify ( ctxPushUName domainUV
                  . ctxPushUName codomainUV
                  . ctxPushDef def )
           body' <- checkAs codomain body
           modify (\(ctx :: Ctx h) -> fromJust (ctxPopEVar param ctx))
           pure (Lambda (Def param domain) body', TypeArrow domain codomain)
    Cst.App callee arg -> do (callee', calleeT) <- check callee
                             (arg', resT) <- checkRedex calleeT arg
                             pure (App callee' arg' resT, resT)
    Cst.IsA expr t -> do {expr' <- checkAs t expr; pure (IsA expr' t, t) }
    Cst.Var name -> do ctx :: Ctx h <- get
                       case ctxLookup name ctx of
                           Just (def @ (Def _ t)) -> pure (Var def, t)
                           Nothing -> throwError (Unbound name :: TypeError h)
    Cst.Const c -> pure (Const c, convert (constType c))

checkRedex :: TypingEffs h r => Type h -> Cst.Expr h -> Eff r (Expr h, Type h)
checkRedex (TypeArrow domain codomain) expr = checkAs domain expr <&> (, domain)

checkAs  :: forall h r . TypingEffs h r => Type h -> Cst.Expr h -> Eff r (Expr h)
checkAs (TypeArrow domain codomain) (Cst.Lambda param Nothing body) =
    do let def = Def param domain
       modify (ctxPushDef def)
       body' <- checkAs codomain body
       modify (\(ctx :: Ctx h) -> fromJust (ctxPopEVar param ctx))
       pure $ Lambda def body'
checkAs t (Cst.Var name) = do ctx :: Ctx h <- get
                              case ctxLookup name ctx of
                                  Just (def @ (Def _ t')) -> checkSub t' t *> pure (Var def)
                                  Nothing -> throwError (Unbound name :: TypeError h)
checkAs t (Cst.Const c) = checkSub (convert (constType c)) t *> pure (Const c)

checkSub :: TypingEffs h r => Type h -> Type h -> Eff r ()
checkSub t @ (TAtom (TypeUName uv)) t' =
    if t == t'
    then pure ()
    else do occursCheck uv t'
            instantiateL uv t'
checkSub t t' @ (TAtom (TypeUName uv)) =
    if t == t'
    then pure ()
    else do occursCheck uv t
            instantiateR t uv
checkSub t t' = error $ show $ "unimplemented:" <+> pretty t <+> "<:" <+> pretty t'

instantiateL :: TypingEffs h r => UVar h -> Type h -> Eff r ()
instantiateL uv = \case
    t @ (TAtom (TypeUName _)) -> do ctx <- get
                                    put =<< fromJust <$> ctxInitUName uv (convert t) ctx

instantiateR :: forall h r . TypingEffs h r => Type h -> UVar h -> Eff r ()
instantiateR t uv =
    case safeConvert t of
        Right (mt :: MonoType h) -> do ctx <- get
                                       put =<< fromJust <$> ctxInitUName uv mt ctx
        Left _ -> undefined

occursCheck :: TypingEffs h r => UVar h -> Type h -> Eff r ()
occursCheck name t @ (TAtom (TypeUName name')) =
    if name == name'
    then throwError $ Occurs name t
    else pure ()
occursCheck name (TAtom (PrimType _)) = pure ()
