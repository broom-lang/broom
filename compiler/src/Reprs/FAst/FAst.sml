structure FAst = struct
    structure Type = FType

    structure Term = struct
        val text = PPrint.text
        val op<> = PPrint.<>
        val op<+> = PPrint.<+>
        val op<++> = PPrint.<++>
        val parens = PPrint.parens
        val brackets = PPrint.brackets
        val braces = PPrint.braces

        type 'typ def = {var: Name.t, typ: 'typ}

        datatype 'typ expr = Fn of Pos.t * 'typ def * 'typ expr
                           | TFn of Pos.t * Type.def * 'typ expr
                           | Extend of Pos.t * 'typ * (Name.t * 'typ expr) vector * 'typ expr option
                           | App of Pos.t * 'typ * {callee: 'typ expr, arg: 'typ expr}
                           | TApp of Pos.t * 'typ * {callee: 'typ expr, arg: 'typ}
                           | Field of Pos.t * 'typ * 'typ expr * Name.t
                           | Let of Pos.t * 'typ stmt vector * 'typ expr
                           | If of Pos.t * 'typ expr * 'typ expr * 'typ expr
                           | Type of Pos.t * 'typ
                           | Use of Pos.t * 'typ def
                           | Const of Pos.t * Const.t

        and 'typ stmt = Val of Pos.t * 'typ def * 'typ expr
                      | Expr of 'typ expr

        val exprPos =
            fn Fn (pos, _, _) => pos
             | TFn (pos, _, _) => pos
             | Extend (pos, _, _, _) => pos
             | App (pos, _, _) => pos
             | TApp (pos, _, _) => pos
             | Field (pos, _, _, _) => pos
             | Let (pos, _, _) => pos
             | If (pos, _, _, _) => pos
             | Type (pos, _) => pos
             | Use (pos, _) => pos
             | Const (pos, _) => pos

       fun defToDoc typeToDoc {var, typ} = Name.toDoc var <> text ":" <+> typeToDoc typ

       fun stmtToDoc typeToDoc =
           fn Val (_, def, valExpr) =>
               text "val" <+> defToDoc typeToDoc def <+> text "="
                   <+> PPrint.align (exprToDoc typeToDoc valExpr)
            | Expr expr => exprToDoc typeToDoc expr

       and fieldToDoc exprToDoc (label, expr) = Name.toDoc label <+> text "=" <+> exprToDoc expr

       and exprToDoc typeToDoc =
           fn Fn (_, param, body) =>
               text "\\" <> defToDoc typeToDoc param <+> text "=>" <+> exprToDoc typeToDoc body
            | TFn (_, param, body) =>
               text "/\\" <> Type.defToDoc param <+> text "=>" <+> exprToDoc typeToDoc body
            | Extend (_, _, fields, record) =>
               braces (PPrint.align (PPrint.punctuate PPrint.newline
                                                      (Vector.map (fieldToDoc (exprToDoc typeToDoc)) fields)
                                     <> (case record
                                         of SOME record => text " with" <+> exprToDoc typeToDoc record
                                          | NONE => PPrint.empty)))
            | App (_, _, {callee, arg}) =>
               parens (exprToDoc typeToDoc callee <+> exprToDoc typeToDoc arg)
            | TApp (_, _, {callee, arg}) =>
               parens (exprToDoc typeToDoc callee <+> brackets (typeToDoc arg))
            | Field (_, _, expr, label) =>
               parens (exprToDoc typeToDoc expr <> text "." <> Name.toDoc label)
            | Let (_, stmts, body) =>
               text "let" <+> PPrint.align (PPrint.punctuate PPrint.newline
                                                             (Vector.map (stmtToDoc typeToDoc) stmts))
               <++> text "in" <+> exprToDoc typeToDoc body
               <++> text "end"
            | If (_, cond, conseq, alt) =>
               text "if" <+> exprToDoc typeToDoc cond
                   <+> text "then" <+> exprToDoc typeToDoc conseq
                   <+> text "else" <+> exprToDoc typeToDoc alt
            | Type (_, t) => brackets (typeToDoc t)
            | Use (_, {var, ...}) => Name.toDoc var 
            | Const (_, c) => Const.toDoc c

        fun exprToString toDoc = PPrint.pretty 80 o toDoc

        fun typeOf (fixT: 'typ Type.typ -> 'typ): 'typ expr -> 'typ =
            fn Fn (pos, {typ = domain, ...}, body) =>
                fixT (Type.Arrow (pos, {domain, codomain = typeOf fixT body}))
             | TFn (pos, param, body) =>
                fixT (Type.ForAll (pos, param, typeOf fixT body))
             | Extend (_, typ, _, _) | App (_, typ, _) | TApp (_, typ, _) => typ
             | Field (_, typ, _, _) => typ
             | Let (_, _, body) => typeOf fixT body
             | Type (pos, t) => fixT (Type.Type (pos, t))
             | Use (_, {typ, ...}) => typ
             | Const (pos, c) => fixT (Type.Prim (pos, Const.typeOf c))

        datatype 'typ binder = ValueBinder of 'typ def * 'typ expr option
                             | TypeBinder of Type.def * 'typ option

        fun foldBinders f acc =
            fn Fn (_, def, _) => f (ValueBinder (def, NONE), acc)
             | TFn (_, def, _) => f (TypeBinder (def, NONE), acc)
             | Let (_, stmts, _) =>
                Vector.foldl (fn (Val (_, def, expr), acc) => f (ValueBinder (def, SOME expr), acc)
                               | (Expr _, acc) => acc)
                             acc stmts
             | Extend _ | App _ | TApp _ | Field _ | Type _ | Use _ | Const _ => acc
    end
end

structure FixedFAst = struct
    structure Type = struct
        open FAst.Type

        datatype typ = Fix of typ FAst.Type.typ

        fun toDoc (Fix t) = FAst.Type.toDoc toDoc t
        val toString = FAst.Type.toString toDoc
    end

    structure Term = struct
        open FAst.Term

        type expr = Type.typ FAst.Term.expr

        val toDoc = FAst.Term.exprToDoc Type.toDoc
        val toString = FAst.Term.exprToString toDoc
        val typeOf = FAst.Term.typeOf Type.Fix
    end
end

