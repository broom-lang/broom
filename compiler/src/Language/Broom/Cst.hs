module Language.Broom.Cst ( Expr(..), Stmt(..), Primop(..), Const(..)
                          , Type(..), MonoType(..), TypeAtom(..), PrimType(..)
                          , constType, primopResType ) where

import Data.Semigroup ((<>))
import Data.Convertible (Convertible, safeConvert)
import Data.Text.Prettyprint.Doc ( Pretty, pretty, (<+>), line, hsep, vsep, parens
                                 , align, indent)
import Data.STRef (STRef)

import Language.Broom.Util (Name)

data Expr h = Lambda Name (Maybe (Type h)) (Expr h)
            | App (Expr h) (Expr h)
            | PrimApp Primop [Expr h]
            | Let [Stmt h] (Expr h)
            | If (Expr h) (Expr h) (Expr h)
            | IsA (Expr h) (Type h)
            | Var Name
            | Const Const

data Stmt h = Val Name (Maybe (Type h)) (Expr h)
            | Expr (Expr h)

data Primop = SafePoint | VarNew | VarInit | VarLoad | Eq | Add | Sub | Mul | Div
            deriving Show

data Const = IntConst Int
           | UnitConst

data Type h = TypeForAll Name (Type h)
            | TypeArrow (Type h) (Type h)
            | TypeApp (Type h) (Type h)
            | TAtom (TypeAtom h)
            deriving Eq

data MonoType h = MTypeArrow (MonoType h) (MonoType h)
                | MTypeApp (MonoType h) (MonoType h)
                | MTAtom (TypeAtom h)
                deriving Eq

data TypeAtom h = TypeName Name
                | TypeUName (STRef h (Maybe (MonoType h)))
                | PrimType PrimType
                deriving Eq

data PrimType = TypeInt
              | TypeBool
              | TypeUnit
              | VarBox
              | TypeMetaCont
              deriving Eq

instance Convertible (Type h) (MonoType h) where
    safeConvert (TAtom a) = pure (MTAtom a)

instance Convertible PrimType (Type h) where
    safeConvert = pure . TAtom . PrimType

constType :: Const -> PrimType
constType = \case
    IntConst _ -> TypeInt
    UnitConst -> TypeUnit

primopResType :: Primop -> [Type h] -> Type h
primopResType op argTypes = case op of
    SafePoint -> TAtom $ PrimType TypeMetaCont
    VarNew -> case argTypes of
                  [argType] -> TypeApp (TAtom $ PrimType VarBox) argType
                  _ -> undefined
    VarInit -> TAtom $ PrimType TypeUnit
    VarLoad -> case argTypes of
                   [TypeApp (TAtom (PrimType VarBox)) contentType] -> contentType
                   _ -> error $ "tried a VarLoad from " <> show (pretty argTypes)
    Add -> TAtom $ PrimType TypeInt
    Sub -> TAtom $ PrimType TypeInt
    Mul -> TAtom $ PrimType TypeInt
    Div -> TAtom $ PrimType TypeInt
    Eq -> TAtom $ PrimType TypeBool

instance Pretty (Expr h) where
    pretty (Lambda param paramType body) =
        "fn" <+> pretty param <> ":" <+> pretty paramType <+> "=>" <+> pretty body
    pretty (App callee arg) = parens $ pretty callee <+> pretty arg
    pretty (PrimApp op args) = parens $ pretty op <+> hsep (fmap pretty args)
    pretty (Let decls body) =
        "let" <+> align (vsep (fmap pretty decls)) <> line <> "in" <> line <>
            indent 4 (pretty body) <> line <> "end"
    pretty (If cond conseq alt) = align ("if" <+> pretty cond <> line <>
                                         "then" <+> pretty conseq <> line <>
                                         "else" <+> pretty alt)
    pretty (IsA expr t) = pretty expr <> ":" <+> pretty t
    pretty (Var name) = pretty name
    pretty (Const c) = pretty c

instance Pretty (Stmt h) where
    pretty (Val pattern t valueExpr) =
        "val" <+> pretty pattern <> ":" <+> pretty t <+> "=" <+> pretty valueExpr
    pretty (Expr expr) = pretty expr

instance Pretty Primop where
    pretty op = "__" <> pretty (show op)

instance Pretty Const where
    pretty (IntConst n) = pretty n
    pretty UnitConst = "()"

instance Pretty (Type h) where
    pretty (TypeForAll param t) =
        "forall" <+> pretty param <+> "." <+> pretty t
    pretty (TypeArrow domain codomain) = pretty domain <+> "->" <+> pretty codomain
    pretty (TypeApp t arg) = parens (pretty t <+> pretty arg)
    pretty (TAtom a) = pretty a

instance Pretty (MonoType h) where
    pretty (MTypeArrow domain codomain) = pretty domain <+> "->" <+> pretty codomain
    pretty (MTypeApp t arg) = parens (pretty t <+> pretty arg)
    pretty (MTAtom a) = pretty a

instance Pretty (TypeAtom h) where
    pretty (TypeName name) = pretty name
    pretty (TypeUName name) = "???" -- FIXME
    pretty (PrimType p) = pretty p

instance Pretty PrimType where
    pretty TypeInt = "Int"
    pretty TypeBool = "Bool"
    pretty TypeUnit = "()"
    pretty VarBox = "__VarBox"
    pretty TypeMetaCont = "__MetaCont"
