signature FAST_TERM = sig
    structure Type: FAST_TYPE

    type 'sv def = {var: Name.t, typ: 'sv Type.concr}

    datatype 'sv expr
        = Fn of Pos.t * 'sv def * 'sv expr
        | TFn of Pos.t * Type.def vector * 'sv expr
        | Extend of Pos.t * 'sv Type.concr  * (Name.t * 'sv expr) vector * 'sv expr option
        | App of Pos.t * 'sv Type.concr * {callee: 'sv expr, arg: 'sv expr}
        | TApp of Pos.t * 'sv Type.concr * {callee: 'sv expr, args: 'sv Type.concr vector}
        | Field of Pos.t * 'sv Type.concr * 'sv expr * Name.t
        | Let of Pos.t * 'sv stmt vector * 'sv expr
        | If of Pos.t * 'sv expr * 'sv expr * 'sv expr
        | Cast of Pos.t * 'sv expr * 'sv Type.co
        | Type of Pos.t * 'sv Type.abs
        | Use of Pos.t * 'sv def
        | Const of Pos.t * Const.t

    and 'sv stmt
        = Val of Pos.t * 'sv def * 'sv expr
        | Axiom of Pos.t * Name.t * 'sv Type.concr
        | Expr of 'sv expr

    val exprPos: 'sv expr -> Pos.t
    val exprToDoc: ('sv -> PPrint.t) -> 'sv expr -> PPrint.t
    val exprToString: ('sv -> PPrint.t) -> 'sv expr -> string
    val stmtsToDoc: ('sv -> PPrint.t) -> 'sv stmt vector -> PPrint.t
end

signature FAST = sig
    structure Type: FAST_TYPE

    structure Term: FAST_TERM
        where type Type.kind = Type.kind
        and type 'sv Type.concr = 'sv Type.concr
        and type 'sv Type.abs = 'sv Type.abs
        and type 'sv Type.co = 'sv Type.co
end

structure FAst :> FAST = struct
    structure Type = FType

    structure Term = struct
        val op|> = Fn.|>
        val text = PPrint.text
        val op<> = PPrint.<>
        val op<+> = PPrint.<+>
        val op<++> = PPrint.<++>
        val space = PPrint.space
        val parens = PPrint.parens
        val brackets = PPrint.brackets
        val braces = PPrint.braces

        structure Type = Type

        type 'sv def = {var: Name.t, typ: 'sv Type.concr}

        datatype 'sv expr
            = Fn of Pos.t * 'sv def * 'sv expr
            | TFn of Pos.t * Type.def vector * 'sv expr
            | Extend of Pos.t * 'sv Type.concr  * (Name.t * 'sv expr) vector * 'sv expr option
            | App of Pos.t * 'sv Type.concr * {callee: 'sv expr, arg: 'sv expr}
            | TApp of Pos.t * 'sv Type.concr * {callee: 'sv expr, args: 'sv Type.concr vector}
            | Field of Pos.t * 'sv Type.concr * 'sv expr * Name.t
            | Let of Pos.t * 'sv stmt vector * 'sv expr
            | If of Pos.t * 'sv expr * 'sv expr * 'sv expr
            | Cast of Pos.t * 'sv expr * 'sv Type.co
            | Type of Pos.t * 'sv Type.abs
            | Use of Pos.t * 'sv def
            | Const of Pos.t * Const.t

        and 'sv stmt
            = Val of Pos.t * 'sv def * 'sv expr
            | Axiom of Pos.t * Name.t * 'sv Type.concr
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
            | Axiom (_, name, typ) =>
               text "axiom" <+> Name.toDoc name <> text ":" <+> Type.Concr.toDoc svarToDoc typ
            | Expr expr => exprToDoc svarToDoc expr

       and stmtsToDoc svarToDoc stmts = PPrint.punctuate PPrint.newline (Vector.map (stmtToDoc svarToDoc) stmts)

       and fieldToDoc svarToDoc (label, expr) = Name.toDoc label <+> text "=" <+> exprToDoc svarToDoc expr

       and exprToDoc svarToDoc =
           let val rec toDoc =
                   fn Fn (_, param, body) =>
                       text "\\" <> defToDoc svarToDoc param <+> text "=>" <+> toDoc body
                    | TFn (_, params, body) =>
                       text "/\\" <> PPrint.punctuate space (Vector.map Type.defToDoc params)
                           <+> text "=>" <+> toDoc body
                    | Extend (_, _, fields, record) =>
                       braces (PPrint.align (PPrint.punctuate PPrint.newline
                                                              (Vector.map (fieldToDoc svarToDoc) fields)
                                             <> (case record
                                                 of SOME record => text " with" <+> toDoc record
                                                  | NONE => PPrint.empty)))
                    | App (_, _, {callee, arg}) =>
                       parens (toDoc callee <+> toDoc arg)
                    | TApp (_, _, {callee, args}) =>
                       parens (toDoc callee <+> (args |> Vector.map (Type.Concr.toDoc svarToDoc)
                                                      |> PPrint.punctuate space
                                                      |> brackets))
                    | Field (_, _, expr, label) =>
                       parens (toDoc expr <> text "." <> Name.toDoc label)
                    | Let (_, stmts, body) =>
                       text "let" <+> PPrint.align (stmtsToDoc svarToDoc stmts)
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

        fun exprToString svarToDoc = PPrint.pretty 80 o exprToDoc svarToDoc

        val rec typeOf =
            fn Fn (pos, {typ = domain, ...}, body) => Type.Arrow (pos, {domain, codomain = typeOf body})
             | TFn (pos, params, body) => Type.ForAll (pos, params, typeOf body)
             | Extend (_, typ, _, _) | App (_, typ, _) | TApp (_, typ, _) => typ
             | Field (_, typ, _, _) => typ
             | Let (_, _, body) => typeOf body
             | If (_, _, conseq, _) => typeOf conseq
             | Type (pos, t) => Type.Type (pos, t)
             | Use (_, {typ, ...}) => typ
             | Const (pos, c) => Type.Prim (pos, Const.typeOf c)
    end
end

signature FLEX_FAST = sig
    structure ScopeId: ID

    structure Type: sig
        structure Prim: PRIM_TYPE where type t = PrimType.t

        datatype kind = datatype FAst.Type.kind
        type def = FAst.Type.def

        datatype concr' = datatype FAst.Type.concr
        datatype abs' = datatype FAst.Type.abs
        datatype co' = datatype FAst.Type.co

        datatype sv = OVar of ov | UVar of uv | Path of path
        withtype concr = sv FAst.Type.concr
        and abs = sv FAst.Type.abs
        and ov = (ScopeId.t, kind) TypeVars.ov
        and uv = (ScopeId.t, sv FAst.Type.concr) TypeVars.uv
        and path = (ScopeId.t, sv FAst.Type.concr, Name.t) TypeVars.path

        val kindToDoc: kind -> PPrint.t
        val svarToDoc: sv -> PPrint.t
        val rowExtTail: concr -> concr
        val unit: Pos.t -> concr

        structure Concr: sig
            val pos: concr -> Pos.t
            val toDoc: concr -> PPrint.t
            val toString: concr -> string
            val tryToUv: concr -> uv option
            val occurs: uv -> concr -> bool
            val pathOccurs: path -> concr -> bool
            val substitute: concr Id.SortedMap.map -> concr -> concr
        end

        structure Abs: sig
            val toDoc: abs -> PPrint.t
            val toString: abs -> string
            val concr: concr -> abs
            val occurs: uv -> abs -> bool
        end
    end

    structure Term: sig
        datatype expr' = datatype FAst.Term.expr
        datatype stmt' = datatype FAst.Term.stmt

        type expr = Type.sv FAst.Term.expr
        type stmt = Type.sv FAst.Term.stmt

        val exprPos: expr -> Pos.t
    end
end

structure FlexFAst :> FLEX_FAST = struct
    structure ScopeId :> ID = Id

    val text = PPrint.text
    val op<> = PPrint.<>

    structure Type = struct
        open FAst.Type

        datatype concr' = datatype FAst.Type.concr
        datatype abs' = datatype FAst.Type.abs
        datatype co' = datatype FAst.Type.co

        datatype sv = OVar of ov | UVar of uv | Path of path
        withtype concr = sv FAst.Type.concr
        and abs = sv FAst.Type.abs
        and ov = (ScopeId.t, kind) TypeVars.ov
        and uv = (ScopeId.t, sv FAst.Type.concr) TypeVars.uv
        and path = (ScopeId.t, sv FAst.Type.concr, Name.t) TypeVars.path

        val rec concrToDoc = fn t => FAst.Type.Concr.toDoc svarToDoc t
        and svarToDoc =
            fn Path path =>
                (case TypeVars.Path.get (Fn.constantly false) path
                 of Either.Right (t, _) => concrToDoc t
                  | Either.Left (t, _) => concrToDoc t)
             | UVar uv =>
                (case TypeVars.Uv.get uv
                 of Either.Right t => concrToDoc t
                  | Either.Left uv => text "^" <> Name.toDoc (TypeVars.Uv.name uv))

        structure Concr = struct
            open Concr

            val toDoc = concrToDoc
            val toString = toString svarToDoc

            fun occurs uv = FAst.Type.Concr.occurs svarOccurs uv
            and svarOccurs uv =
                fn UVar uv' => (case TypeVars.Uv.get uv'
                                of Either.Left uv' => TypeVars.Uv.eq (uv, uv')
                                 | Either.Right t => occurs uv t)

            fun pathOccurs path = FAst.Type.Concr.occurs pathSvarOccurs path
            and pathSvarOccurs path =
                fn Path path' => TypeVars.Path.eq (path', path)

            fun substitute kv = FAst.Type.Concr.substitute svarSubstitute kv
            and svarSubstitute kv =
                fn UVar uv => (case TypeVars.Uv.get uv
                               of Either.Left _ => NONE
                                | Either.Right t => SOME (substitute kv t))

            val tryToUv =
                fn SVar (_, UVar uv) => SOME uv
                 | _ => NONE
        end

        structure Abs = struct
            open Abs

            val toDoc = toDoc svarToDoc
            val toString = toString svarToDoc

            val occurs = occurs Concr.svarOccurs
            val substitute = substitute Concr.svarSubstitute
        end
    end

    structure Term = struct
        structure Typ = Type
        open FAst.Term
        structure Type = Typ

        datatype expr' = datatype FAst.Term.expr
        datatype stmt' = datatype FAst.Term.stmt

        type expr = Type.sv expr
        type stmt = Type.sv stmt

        val exprToDoc: expr -> PPrint.t = exprToDoc Type.svarToDoc
        val exprToString: expr -> string = exprToString Type.svarToDoc
    end
end

structure FixedFAst = struct
    structure Type = struct
        open FAst.Type

        type sv = Nothing.t
        type concr = sv concr
        type abs = sv abs

        val svarToDoc = PPrint.text o Nothing.toString

        val concrToString: concr -> string = FAst.Type.Concr.toString svarToDoc

        structure Concr = struct
            open Concr

            val substitute: concr Id.SortedMap.map -> concr -> concr = substitute (fn _ => fn _ => NONE)
            val kindOf: concr -> kind = kindOf (fn _ => raise Fail "unreachable")
            val toString = concrToString
        end

        structure Abs = struct
            open Abs

            val substitute: concr Id.SortedMap.map -> abs -> abs = substitute (fn _ => fn _ => NONE)
        end
    end

    structure Term = struct
        structure Typ = Type
        open FAst.Term
        structure Type = Typ

        type expr = Type.sv expr
        type stmt = Type.sv stmt

        val exprToDoc: expr -> PPrint.t = FAst.Term.exprToDoc Type.svarToDoc
        val exprToString: expr -> string = FAst.Term.exprToString Type.svarToDoc
        val stmtsToDoc = FAst.Term.stmtsToDoc Type.svarToDoc
    end
end

