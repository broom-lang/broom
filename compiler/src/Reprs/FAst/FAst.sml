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

        type 'sv def = {var: Name.t, typ: 'sv Type.concr}

        datatype 'sv expr
            = Fn of Pos.t * 'sv def * 'sv expr
            | TFn of Pos.t * Type.def * 'sv expr
            | Extend of Pos.t * 'sv Type.concr  * (Name.t * 'sv expr) vector * 'sv expr option
            | App of Pos.t * 'sv Type.concr * {callee: 'sv expr, arg: 'sv expr}
            | TApp of Pos.t * 'sv Type.concr * {callee: 'sv expr, arg: 'sv Type.abs}
            | Field of Pos.t * 'sv Type.concr * 'sv expr * Name.t
            | Let of Pos.t * 'sv stmt vector * 'sv expr
            | If of Pos.t * 'sv expr * 'sv expr * 'sv expr
            | Type of Pos.t * 'sv Type.abs
            | Use of Pos.t * 'sv def
            | Const of Pos.t * Const.t

        and 'sv stmt
            = Val of Pos.t * 'sv def * 'sv expr
            | Expr of 'sv expr

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

       fun defToDoc svarToDoc {var, typ} = Name.toDoc var <> text ":" <+> Type.Concr.toDoc svarToDoc typ

       fun stmtToDoc svarToDoc =
           fn Val (_, def, valExpr) =>
               text "val" <+> defToDoc svarToDoc def <+> text "="
                   <+> PPrint.align (exprToDoc svarToDoc valExpr)
            | Expr expr => exprToDoc svarToDoc expr

       and fieldToDoc svarToDoc (label, expr) = Name.toDoc label <+> text "=" <+> exprToDoc svarToDoc expr

       and exprToDoc svarToDoc =
           let val rec toDoc =
                   fn Fn (_, param, body) =>
                       text "\\" <> defToDoc svarToDoc param <+> text "=>" <+> toDoc body
                    | TFn (_, param, body) =>
                       text "/\\" <> Type.defToDoc param <+> text "=>" <+> toDoc body
                    | Extend (_, _, fields, record) =>
                       braces (PPrint.align (PPrint.punctuate PPrint.newline
                                                              (Vector.map (fieldToDoc svarToDoc) fields)
                                             <> (case record
                                                 of SOME record => text " with" <+> toDoc record
                                                  | NONE => PPrint.empty)))
                    | App (_, _, {callee, arg}) =>
                       parens (toDoc callee <+> toDoc arg)
                    | TApp (_, _, {callee, arg}) =>
                       parens (toDoc callee <+> brackets (Type.Abs.toDoc svarToDoc arg))
                    | Field (_, _, expr, label) =>
                       parens (toDoc expr <> text "." <> Name.toDoc label)
                    | Let (_, stmts, body) =>
                       text "let" <+> PPrint.align (PPrint.punctuate PPrint.newline
                                                                     (Vector.map (stmtToDoc svarToDoc) stmts))
                       <++> text "in" <+> toDoc body
                       <++> text "end"
                    | If (_, cond, conseq, alt) =>
                       text "if" <+> toDoc cond
                           <+> text "then" <+> toDoc conseq
                           <+> text "else" <+> toDoc alt
                    | Type (_, t) => brackets (Type.Abs.toDoc svarToDoc t)
                    | Use (_, {var, ...}) => Name.toDoc var 
                    | Const (_, c) => Const.toDoc c
            in toDoc
            end

        fun exprToString toDoc = PPrint.pretty 80 o toDoc

        val rec typeOf =
            fn Fn (pos, {typ = domain, ...}, body) => Type.Arrow (pos, {domain, codomain = typeOf body})
             | TFn (pos, param, body) => Type.ForAll (pos, param, typeOf body)
             | Extend (_, typ, _, _) | App (_, typ, _) | TApp (_, typ, _) => typ
             | Field (_, typ, _, _) => typ
             | Let (_, _, body) => typeOf body
             | Type (pos, t) => Type.Type (pos, t)
             | Use (_, {typ, ...}) => typ
             | Const (pos, c) => Type.Prim (pos, Const.typeOf c)

        datatype 'sv binder = ValueBinder of 'sv def * 'sv expr option
                            | TypeBinder of Type.def * 'sv Type.concr option

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
    end

    structure Term = struct
        open FAst.Term
    end
end

