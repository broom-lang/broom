module Language.Broom.Cst ( Expr(..), Stmt(..), Primop(..), Const(..)
                          , Type(..), MonoType(..), TypeAtom(..), PrimType(..)
                          , constType, primopResType ) where

import Data.Data (Data, Typeable)

import Data.Semigroup ((<>))
import Data.Convertible (Convertible, safeConvert)
import Data.Text.Prettyprint.Doc ( Pretty, pretty, (<+>), line, hsep, vsep, parens
                                 , align, indent)

import Language.Broom.Util (Name)

data Expr = Lambda Name (Maybe Type) Expr
          | App Expr Expr
          | PrimApp Primop [Expr]
          | Let [Stmt] Expr
          | If Expr Expr Expr
          | IsA Expr Type
          | Var Name
          | Const Const
          deriving (Data, Typeable)

data Stmt = Val Name (Maybe Type) Expr
          | Expr Expr
          deriving (Data, Typeable)

data Primop = SafePoint | VarNew | VarInit | VarLoad | Eq | Add | Sub | Mul | Div
            deriving (Show, Data, Typeable)

data Const = IntConst Int
           | UnitConst
           deriving (Data, Typeable)

data Type = TypeForAll Name Type
          | TypeArrow Type Type
          | TypeApp Type Type
          | TAtom TypeAtom
          deriving (Eq, Data, Typeable)

data MonoType = MTypeArrow MonoType MonoType
              | MTypeApp MonoType MonoType
              | MTAtom TypeAtom
              deriving (Eq, Data, Typeable)

data TypeAtom = TypeName Name
              | TypeUName Name
              | PrimType PrimType
              deriving (Eq, Data, Typeable)

data PrimType = TypeInt
              | TypeBool
              | TypeUnit
              | VarBox
              | TypeMetaCont
              deriving (Eq, Data, Typeable)

instance Convertible Type MonoType where
    safeConvert (TAtom a) = pure (MTAtom a)

instance Convertible PrimType Type where
    safeConvert = pure . TAtom . PrimType

constType :: Const -> PrimType
constType = \case
    IntConst _ -> TypeInt
    UnitConst -> TypeUnit

primopResType :: Primop -> [Type] -> Type
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

instance Pretty Expr where
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

instance Pretty Stmt where
    pretty (Val pattern t valueExpr) =
        "val" <+> pretty pattern <> ":" <+> pretty t <+> "=" <+> pretty valueExpr
    pretty (Expr expr) = pretty expr

instance Pretty Primop where
    pretty op = "__" <> pretty (show op)

instance Pretty Const where
    pretty (IntConst n) = pretty n
    pretty UnitConst = "()"

instance Pretty Type where
    pretty (TypeForAll param t) =
        "forall" <+> pretty param <+> "." <+> pretty t
    pretty (TypeArrow domain codomain) = pretty domain <+> "->" <+> pretty codomain
    pretty (TypeApp t arg) = parens (pretty t <+> pretty arg)
    pretty (TAtom a) = pretty a

instance Pretty MonoType where
    pretty (MTypeArrow domain codomain) = pretty domain <+> "->" <+> pretty codomain
    pretty (MTypeApp t arg) = parens (pretty t <+> pretty arg)
    pretty (MTAtom a) = pretty a

instance Pretty TypeAtom where
    pretty (TypeName name) = pretty name
    pretty (TypeUName name) = pretty name
    pretty (PrimType p) = pretty p

instance Pretty PrimType where
    pretty TypeInt = "Int"
    pretty TypeBool = "Bool"
    pretty TypeUnit = "()"
    pretty VarBox = "__VarBox"
    pretty TypeMetaCont = "__MetaCont"
