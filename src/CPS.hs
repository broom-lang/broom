module CPS ( Block(..), Transfer(..), Stmt(..), Expr(..), Atom(..), Type(..), primopResType ) where

import Data.Semigroup ((<>))
import Data.Convertible (Convertible, safeConvert)
import Data.Text.Prettyprint.Doc ( Pretty, pretty, line, (<+>), hsep, vsep, indent
                                 , parens, braces )

import Util (Name)
import qualified Ast
import Ast (Primop(..), Const(..))

data Block = Block [Stmt] Transfer

data Transfer = App Name [Atom]
              | If Atom Block Block

data Stmt = Def Name Type Expr
          | Expr Expr

data Expr = Fn [(Name, Type)] Block
          | PrimApp Primop [Atom]
          | Atom Atom

data Atom = Use Name
          | Const Const

data Type = TypeForAll Name Type
          | FnType [Type]
          | TypeName Name
          | PrimType Ast.PrimType

instance Convertible Ast.Type Type where
    safeConvert = \case
        Ast.TypeForAll param t -> TypeForAll param <$> safeConvert t
        Ast.TypeArrow domain codomain ->
            do domain' <- safeConvert domain
               codomain' <- safeConvert codomain
               pure $ FnType [FnType [codomain'], domain']
        Ast.TypeName name -> pure (TypeName name)
        Ast.PrimType p -> pure (PrimType p)

primopResType :: Primop -> Type
primopResType = PrimType . \case
    Add -> Ast.TypeInt
    Sub -> Ast.TypeInt
    Mul -> Ast.TypeInt
    Div -> Ast.TypeInt
    Eq -> Ast.TypeBool

instance Pretty Block where
    pretty (Block stmts transfer) =
        let prettyStmts = fmap (\stmt -> pretty stmt <> ";") stmts
        in braces (line <> indent 4 (vsep (prettyStmts <> [pretty transfer])) <> line)

instance Pretty Stmt where
    pretty = \case Def name t expr ->
                       pretty name <> ":" <+> pretty t <+> "=" <+> pretty expr
                   Expr expr -> pretty expr

instance Pretty Transfer where
    pretty = \case App dest args -> pretty dest <+> hsep (fmap pretty args)
                   If cond dest alt ->
                       "if" <+> pretty cond <+> pretty dest <+> pretty alt

instance Pretty Expr where
    pretty = \case Fn params body ->
                       "fn" <+> hsep (fmap prettyParam params) <+>
                           pretty body
                       where prettyParam (name, t) = pretty name <> ":" <+> pretty t
                   PrimApp op args -> pretty op <+> hsep (fmap pretty args)
                   Atom a -> pretty a

instance Pretty Atom where
    pretty (Use name) = pretty name
    pretty (Const c) = pretty c

instance Pretty Type where
    pretty = \case TypeForAll param t ->
                       "forall" <+> pretty param <+> "." <+> pretty t
                   FnType domains -> parens ("fn" <+> hsep (fmap pretty domains))
                   TypeName name -> pretty name
                   PrimType p -> pretty p
