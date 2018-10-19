{-# LANGUAGE ConstraintKinds #-}

module Language.Broom.Typecheck (TypeError, Expr, Stmt, typecheck) where

import qualified Debug.Trace as DT

import Data.Foldable (foldl')
import Data.Semigroup ((<>))
import Data.Convertible (Convertible, safeConvert, convert)
import Data.Maybe (fromJust)
import Data.STRef (STRef, newSTRef, writeSTRef, readSTRef)
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

instance Convertible (UVar h) (MonoType h) where
    safeConvert = pure . MTAtom . TypeUName

freshUV :: Lifted (ST h) r => Eff r (UVar h)
freshUV = lift (newSTRef Nothing)

-- TODO: Path compression
findUV :: Lifted (ST h) r => UVar h -> Eff r (Either (MonoType h) (UVar h))
findUV uv = lift (readSTRef uv) >>= \case
    Just (MTAtom (TypeUName uv')) -> findUV uv'
    Just mt -> pure (Left mt)
    Nothing -> pure (Right uv)

writeUV :: Lifted (ST h) r => UVar h -> MonoType h -> Eff r ()
writeUV uv mt = findUV uv >>= \case
    Left _ -> error "tried to reinitialize UVar"
    Right uv' -> lift $ writeSTRef uv' (Just mt)

readUV :: Lifted (ST h) r => UVar h -> Eff r (Maybe (MonoType h))
readUV uv = findUV uv <&> \case
    Left mt -> Just mt
    Right _ -> Nothing

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
ctxInitUName uv mt ctx @ (Ctx entries) = init entries
    where init [] = pure Nothing
          init (UVar uv' : es) | uv == uv' = writeUV uv mt *> pure (Just ctx)
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
typecheck expr = runError (evalState (builtinCtx :: Ctx h) m)
    where m = do (expr, _) <- check expr
                 removeUVars expr

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
checkRedex (TypeArrow domain codomain) expr = checkAs domain expr <&> (, codomain)

checkAs  :: forall h r . TypingEffs h r => Type h -> Cst.Expr h -> Eff r (Expr h)
checkAs (TypeArrow domain codomain) (Cst.Lambda param Nothing body) =
    do let def = Def param domain
       modify (ctxPushDef def)
       body' <- checkAs codomain body
       modify (\(ctx :: Ctx h) -> fromJust (ctxPopEVar param ctx))
       pure $ Lambda def body'
checkAs t expr @ (Cst.App _ _) = do (expr', exprT) <- check expr
                                    checkSub exprT t *> pure expr'
checkAs t (Cst.Var name) = do ctx :: Ctx h <- get
                              case ctxLookup name ctx of
                                  Just (def @ (Def _ t')) -> checkSub t' t *> pure (Var def)
                                  Nothing -> throwError (Unbound name :: TypeError h)
checkAs t (Cst.Const c) = checkSub (convert (constType c)) t *> pure (Const c)

checkSub :: TypingEffs h r => Type h -> Type h -> Eff r ()
checkSub (TAtom (TypeUName uv)) (TAtom (TypeUName uv')) = undefined
checkSub (TAtom (TypeUName uv)) t' =
    findUV uv >>= \case
        Left mt -> undefined
        Right uv' -> do occursCheck uv' t'
                        instantiateL uv' t'
checkSub t t' @ (TAtom (TypeUName uv')) =
    findUV uv' >>= \case
        Left mt -> undefined
        Right uv'' -> do occursCheck uv'' t
                         instantiateR t uv''
checkSub t t' = error $ show $ "unimplemented:" <+> pretty t <+> "<:" <+> pretty t'

instantiateL :: TypingEffs h r => UVar h -> Type h -> Eff r ()
instantiateL uv t' = DT.traceM ("iL " <> show (pretty t')) *> case t' of
    TAtom (TypeUName uv') -> findUV uv' >>= \case
        Left mt -> do ctx <- get
                      put =<< fromJust <$> ctxInitUName uv mt ctx
        Right uv'' -> do ctx <- get
                         put =<< fromJust <$> ctxInitUName uv'' (convert uv) ctx
    t -> case safeConvert t of
             Left _ -> undefined
             Right mt -> do ctx <- get
                            put =<< fromJust <$> ctxInitUName uv mt ctx

instantiateR :: forall h r . TypingEffs h r => Type h -> UVar h -> Eff r ()
instantiateR t uv' = DT.traceM ("iR " <> show (pretty t)) *> case t of
    TAtom (TypeUName uv) -> findUV uv >>= \case
        Left mt -> do ctx <- get
                      put =<< fromJust <$> ctxInitUName uv' mt ctx
    t -> case safeConvert t of
             Left _ -> undefined
             Right mt -> do ctx <- get
                            put =<< fromJust <$> ctxInitUName uv' mt ctx

occursCheck :: TypingEffs h r => UVar h -> Type h -> Eff r ()
occursCheck name t @ (TAtom (TypeUName name')) =
    if name == name'
    then throwError $ Occurs name t
    else pure ()
occursCheck name (TAtom (PrimType _)) = pure ()

class RemoveUVars a b where
    removeUVars :: Lifted (ST h) r => a h -> Eff r (b h)

instance RemoveUVars Expr Expr where
    removeUVars = \case
        Lambda def body -> Lambda <$> removeUVars def <*> removeUVars body
        App callee arg t -> App <$> removeUVars callee <*> removeUVars arg <*> removeUVars t
        Var def -> Var <$> removeUVars def
        c @ (Const _) -> pure c

instance RemoveUVars Def Def where
    removeUVars (Def name t) = Def name <$> removeUVars t

instance RemoveUVars Type Type where
    removeUVars = \case
        TAtom at -> removeUVars at

instance RemoveUVars MonoType Type where
    removeUVars = \case
        MTAtom at -> removeUVars at

instance RemoveUVars TypeAtom Type where
    removeUVars = \case
        t @ (TypeName _) -> TAtom <$> pure t
        TypeUName uv -> readUV uv >>= \case
            Just mt -> removeUVars mt
            -- Instantiation was never required, choose something arbitrary:
            Nothing -> pure $ TAtom (PrimType TypeUnit)
        t @ (PrimType _) -> TAtom <$> pure t
