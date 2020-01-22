signature FAST_TYPE = sig
    structure Id: ID
        where type t = FTypeBase.Id.t
        where type 'v SortedMap.map = 'v FTypeBase.Id.SortedMap.map
    structure Prim: PRIM_TYPE where type t = PrimType.t
    structure ScopeId: ID

    type kind = Kind.t

    type def = FTypeBase.def

    datatype effect = datatype FTypeBase.effect
    type arrow = FTypeBase.arrow

    datatype concr' = datatype FTypeBase.concr
    datatype co' = datatype FTypeBase.co

    datatype sv = UVar of uv | Path of path
    withtype uv = sv FTypeBase.concr TypeVars.uv
    and path = sv FTypeBase.concr TypeVars.path

    type concr = sv FTypeBase.concr
    type row = sv FTypeBase.row
    type co = sv FTypeBase.co

    type ('expr, 'error) env = (concr, 'expr, 'error) TypecheckingEnv.t

    val defToDoc: def -> PPrint.t
    val arrowDoc: arrow -> PPrint.t
    val svarToDoc: ('expr, 'error) env -> sv -> PPrint.t
    val rowExtBase: concr -> concr
    val piEffect: concr -> effect option
    val kindDefault: kind -> concr
    val primopType : Primop.t -> def vector * effect * { domain: concr vector
                                                       , codomain: concr * bool }

    structure Concr: sig
        type t = concr

        val toDoc: ('expr, 'error) env -> concr -> PPrint.t
        val toString : ('expr, 'error) env -> concr -> string
        val isSmall : concr -> bool
        val occurs : ('expr, 'error) env -> uv -> concr -> bool
        val substitute: ('expr, 'error) env -> concr Id.SortedMap.map -> concr -> concr
        val rewriteRow : Name.t -> concr -> row option
        val kindOf : (sv -> kind) -> concr -> kind
    end

    structure Co: sig
        val toDoc: ('expr, 'error) env -> co -> PPrint.t
    end
end

signature FAST_TERM = sig
    structure Type: FAST_TYPE
    type 'a vector1 = 'a Vector1.vector
    type ('expr, 'error) env

    type arrow = Type.arrow

    type def = {pos: Pos.span, id: DefId.t, var: Name.t, typ: Type.concr}

    datatype expr
        = Fn of Pos.span * def * arrow * expr
        | TFn of Pos.span * Type.def vector1 * expr
        | EmptyRecord of Pos.span
        | With of Pos.span * Type.concr * {base : expr, field : Name.t * expr}
        | Without of Pos.span * Type.concr * {base : expr, field : Name.t}
        | Where of Pos.span * Type.concr * {base : expr, field : Name.t * expr}
        | App of Pos.span * Type.concr * {callee: expr, arg: expr}
        | TApp of Pos.span * Type.concr * {callee: expr, args: Type.concr vector1}
        | PrimApp of Pos.span * Type.concr * Primop.t * Type.concr vector * expr vector
            * ({def : def, body : expr} * expr) option
        | Field of Pos.span * Type.concr * expr * Name.t
        | Letrec of Pos.span * stmt vector1 * expr
        | Let of Pos.span * stmt vector1 * expr
        | Match of Pos.span * Type.concr * expr * clause vector
        | Cast of Pos.span * Type.concr * expr * Type.co
        | Type of Pos.span * Type.concr
        | Use of Pos.span * def
        | Const of Pos.span * Const.t

    and stmt
        = Val of Pos.span * def * expr
        | Axiom of Pos.span * Name.t * Type.concr * Type.concr
        | Expr of expr

    and pat
        = Def of Pos.span * def
        | AnyP of Pos.span
        | ConstP of Pos.span * Const.t

    withtype clause = {pattern: pat, body: expr}

    type program = { typeFns: Type.def vector
                   , code: Pos.span * stmt vector1 * expr
                   , sourcemap: Pos.sourcemap }
   
    val exprPos: expr -> Pos.span
    val stmtPos: stmt -> Pos.span
    val patPos: pat -> Pos.span

    val typeOf: expr -> Type.concr

    val updateDefTyp : {pos: Pos.span, id: DefId.t, var: Name.t, typ: 't} -> ('t -> 'u)
                     -> {pos: Pos.span, id: DefId.t, var: Name.t, typ: 'u}
    val setDefTyp : {pos: Pos.span, id: DefId.t, var: Name.t, typ: 't} -> 'u
                  -> {pos: Pos.span, id: DefId.t, var: Name.t, typ: 'u}

    val defToDoc : ('expr, 'error) env -> def -> PPrint.t
    val exprToDoc: ('expr, 'error) env -> expr -> PPrint.t
    val exprToString: ('expr, 'error) env -> expr -> string
    val stmtToDoc: ('expr, 'error) env -> stmt -> PPrint.t
    val stmtsToDoc: ('expr, 'error) env -> stmt vector -> PPrint.t
    val patternToDoc: ('expr, 'error) env -> pat -> PPrint.t
    val programToDoc: ('expr, 'error) env -> program -> PPrint.t
end

structure FAst :> sig
    structure Type : FAST_TYPE
    structure Term : FAST_TERM
        where type Type.sv = Type.sv
        where type ('expr, 'error) env = ('expr, 'error) Type.env
end = struct
    structure Type = struct
        open FTypeBase
        structure ScopeId = ScopeId

        val text = PPrint.text
        val op<> = PPrint.<>

        datatype concr' = datatype FTypeBase.concr
        datatype co' = datatype FTypeBase.co

        datatype sv = UVar of uv | Path of path
        withtype concr = sv FTypeBase.concr
        and co = sv FTypeBase.co
        and uv = sv FTypeBase.concr TypeVars.uv
        and path = sv FTypeBase.concr TypeVars.path

        type row = sv FTypeBase.row

        type ('expr, 'error) env = (concr, 'expr, 'error) TypecheckingEnv.t

        fun concrToDoc env = fn t => FTypeBase.Concr.toDoc (svarToDoc env) t
        and svarToDoc env =
            fn Path path =>
                (case TypeVars.Path.get env path
                 of Either.Right (uv, _) => uvToDoc env uv
                  | Either.Left t => text "^^" <> PPrint.parens (concrToDoc env t))
             | UVar uv => uvToDoc env uv
        and uvToDoc env uv =
            case TypeVars.Uv.get env uv
            of Either.Right t => concrToDoc env t
             | Either.Left uv => text "^" <> Name.toDoc (TypeVars.Uv.name env uv)

        structure Concr = struct
            open Concr

            type t = concr

            val toDoc = concrToDoc
            fun toString env = Concr.toString (svarToDoc env)

            fun occurs env uv = FTypeBase.Concr.occurs (svarOccurs env) uv
            and svarOccurs env uv =
                fn Path path =>
                    (case TypeVars.Path.get env path
                     of Either.Left t => occurs env uv t
                      | Either.Right (uv', _) => uvOccurs env uv uv')
                 | UVar uv' => uvOccurs env uv uv'
            and uvOccurs env uv uv' =
                case TypeVars.Uv.get env uv'
                of Either.Left uv' => TypeVars.Uv.eq (uv, uv')
                 | Either.Right t => occurs env uv t

            fun substitute env kv = FTypeBase.Concr.substitute (svarSubstitute env) kv
            and svarSubstitute env kv =
                fn Path path =>
                    (case TypeVars.Path.get env path
                     of Either.Left _ => NONE (* FIXME? *)
                      | Either.Right (uv, _) => uvSubstitute env kv uv)
                 | UVar uv => uvSubstitute env kv uv
            and uvSubstitute env kv uv =
                case TypeVars.Uv.get env uv
                of Either.Left _ => NONE
                 | Either.Right t => SOME (substitute env kv t)
        end

        structure Co = struct
            open Co

            fun toDoc env = Co.toDoc (svarToDoc env)
        end
    end

    structure Term = struct
        val op|> = Fn.|>
        val text = PPrint.text
        val op<> = PPrint.<>
        val op<+> = PPrint.<+>
        val op<++> = PPrint.<++>
        val op<|> = PPrint.<|>
        val space = PPrint.space
        val newline = PPrint.newline
        val parens = PPrint.parens
        val brackets = PPrint.brackets
        val braces = PPrint.braces
        val punctuate = PPrint.punctuate
        val align = PPrint.align

        structure Type = Type
        type 'a vector1 = 'a Vector1.vector
        type ('expr, 'error) env = ('expr, 'error) Type.env

        type arrow = Type.arrow

        type def = {pos: Pos.span, id: DefId.t, var: Name.t, typ: Type.concr}

        datatype expr
            = Fn of Pos.span * def * arrow * expr
            | TFn of Pos.span * Type.def vector1 * expr
            | EmptyRecord of Pos.span
            | With of Pos.span * Type.concr * {base : expr, field : Name.t * expr}
            | Without of Pos.span * Type.concr * {base : expr, field : Name.t}
            | Where of Pos.span * Type.concr * {base : expr, field : Name.t * expr}
            | App of Pos.span * Type.concr * {callee: expr, arg: expr}
            | TApp of Pos.span * Type.concr * {callee: expr, args: Type.concr vector1}
            | PrimApp of Pos.span * Type.concr * Primop.t * Type.concr vector * expr vector
                * ({def : def, body : expr} * expr) option
            | Field of Pos.span * Type.concr * expr * Name.t
            | Letrec of Pos.span * stmt vector1 * expr
            | Let of Pos.span * stmt vector1 * expr
            | Match of Pos.span * Type.concr * expr * clause vector
            | Cast of Pos.span * Type.concr * expr * Type.co
            | Type of Pos.span * Type.concr
            | Use of Pos.span * def
            | Const of Pos.span * Const.t

        and stmt
            = Val of Pos.span * def * expr
            | Axiom of Pos.span * Name.t * Type.concr * Type.concr
            | Expr of expr

        and pat
            = Def of Pos.span * def
            | AnyP of Pos.span
            | ConstP of Pos.span * Const.t

        withtype clause = {pattern: pat, body: expr}

        val exprPos =
            fn Fn (pos, _, _, _) => pos
             | TFn (pos, _, _) => pos
             | EmptyRecord pos => pos
             | With (pos, _, _) => pos
             | Without (pos, _, _) => pos
             | Where (pos, _, _) => pos
             | App (pos, _, _) => pos
             | PrimApp (pos, _, _, _, _, _) => pos
             | TApp (pos, _, _) => pos
             | Field (pos, _, _, _) => pos
             | Letrec (pos, _, _) => pos
             | Let (pos, _, _) => pos
             | Match (pos, _, _, _) => pos
             | Cast (pos, _, _, _) => pos
             | Type (pos, _) => pos
             | Use (pos, _) => pos
             | Const (pos, _) => pos

        type program = { typeFns: Type.def vector
                       , code: Pos.span * stmt vector1 * expr
                       , sourcemap: Pos.sourcemap }

        fun updateDefTyp {pos, id, var, typ} f = {pos, id, var, typ = f typ}
        fun setDefTyp def typ' = updateDefTyp def (Fn.constantly typ')

       fun defToDoc env {pos = _, id = _, var, typ} =
           Name.toDoc var <> text ":" <+> Type.Concr.toDoc env typ

       fun stmtToDoc env =
           fn Val (_, def, valExpr) =>
               let val lhs = text "val" <+> defToDoc env def <+> text "="
                   val rhs = PPrint.align (exprToDoc env valExpr)
               in lhs <> (space <> rhs <|> PPrint.nest 4 (newline <> rhs))
               end
            | Axiom (_, name, l, r) =>
               text "axiom" <+> Name.toDoc name <+> text ":"
               <+> Type.Concr.toDoc env l <+> text "~" <+> Type.Concr.toDoc env r
            | Expr expr => exprToDoc env expr

       and stmtsToDoc env =
           fn stmts => PPrint.punctuate PPrint.newline (Vector.map (stmtToDoc env) stmts)

       and fieldToDoc env =
           fn (label, expr) => Name.toDoc label <+> text "=" <+> exprToDoc env expr

       and exprToDoc env =
           fn Fn (_, param, arrow, body) =>
               text "\\" <> defToDoc env param <+> Type.arrowDoc arrow <+> exprToDoc env body
            | TFn (_, params, body) =>
               text "/\\" <> PPrint.punctuate1 space (Vector1.map Type.defToDoc params)
                   <+> text "=>" <+> exprToDoc env body
            | EmptyRecord _ => text "{}"
            | With (_, _, {base, field = (label, fieldExpr)}) =>
               braces(exprToDoc env base <+> text "with" <+> Name.toDoc label
                      <+> text "=" <+> exprToDoc env fieldExpr)
            | Without (_, _, {base, field = label}) =>
               braces(exprToDoc env base <+> text "without" <+> Name.toDoc label)
            | Where (_, _, {base, field = (label, fieldExpr)}) =>
               braces(exprToDoc env base <+> text "where" <+> Name.toDoc label
                      <+> text "=" <+> exprToDoc env fieldExpr)
            | App (_, _, {callee, arg}) =>
               parens (exprToDoc env callee <+> exprToDoc env arg)
            | TApp (_, _, {callee, args}) =>
               parens (exprToDoc env callee <+> (args
                                                |> Vector1.map (Type.Concr.toDoc env)
                                                |> PPrint.punctuate1 space
                                                |> brackets))
            | PrimApp (_, _, opn, targs, args, clauses) =>
               parens (Primop.toDoc opn
                       <+> brackets (punctuate (text "," <> space) (Vector.map (Type.Concr.toDoc env) targs))
                       <+> punctuate space (Vector.map (exprToDoc env) args)
                       <> (case clauses
                           of SOME ({def, body}, failure) =>
                               PPrint.nest 4 (newline <> text "|" <+> defToDoc env def <+> text "->" <+> exprToDoc env body
                                              <++> text "|" <+> text "->" <+> exprToDoc env failure)
                            | NONE => PPrint.empty))
            | Field (_, _, expr, label) =>
               parens (exprToDoc env expr <> text "." <> Name.toDoc label)
            | Letrec (_, stmts, body) =>
               text "letrec" <+> PPrint.align (stmtsToDoc env (Vector1.toVector stmts))
               <++> text "in" <+> align (exprToDoc env body)
               <++> text "end"
            | Let (_, stmts, body) =>
               text "let" <+> PPrint.align (stmtsToDoc env (Vector1.toVector stmts))
               <++> text "in" <+> align (exprToDoc env body)
               <++> text "end"
            | Match (_, _, matchee, clauses) =>
                text "match" <+> exprToDoc env matchee
                    <+> braces (newline <> clausesToDoc env clauses)
            | Cast (_, _, expr, co) => exprToDoc env expr <+> text "via" <+> Type.Co.toDoc env co
            | Type (_, t) => brackets (Type.Concr.toDoc env t)
            | Use (_, {var, ...}) => Name.toDoc var 
            | Const (_, c) => Const.toDoc c

        and recordToDoc env =
            fn curtain => fn (_, _, fields, record) =>
                let val fieldDocs = Vector.map (fieldToDoc env) fields
                    val oneLiner = braces (punctuate (text "," <> space) fieldDocs
                                           <> (case record
                                               of SOME record =>
                                                   space <> text curtain <+> exprToDoc env record
                                                | NONE => PPrint.empty))
                    val multiLiner =
                        align (braces (space
                                       <> punctuate (newline <> text "," <> space) fieldDocs
                                       <> (case record
                                           of SOME record =>
                                               newline <> text curtain <+> exprToDoc env record
                                            | NONE => PPrint.empty)
                                       <> space))
                in oneLiner <|> multiLiner
                end

        and clausesToDoc env clauses = PPrint.punctuate newline (Vector.map (clauseToDoc env) clauses)

        and clauseToDoc env {pattern, body} =
            patternToDoc env pattern <+> text "->" <+> exprToDoc env body

        and patternToDoc env =
            fn Def (_, def) => defToDoc env def
             | AnyP _ => text "_"
             | ConstP (_, c) => Const.toDoc c

        fun exprToString env = PPrint.pretty 80 o exprToDoc env

        val stmtPos =
            fn Val (pos, _, _) => pos
             | Axiom (pos, _, _, _) => pos
             | Expr expr => exprPos expr

        val patPos =
            fn Def (pos, _) => pos
             | AnyP pos => pos
             | ConstP (pos, _) => pos

        fun typeFnToDoc def = text "type" <+> Type.defToDoc def

        fun axiomToDoc env (name, l, r) =
            text "axiom" <+> Name.toDoc name <> text ":"
                <+> Type.Concr.toDoc env l <+> text "~" <+> Type.Concr.toDoc env r

        fun programToDoc env {typeFns, code = (_, stmts, body), sourcemap = _} =
            punctuate (newline <> newline) (Vector.map typeFnToDoc typeFns)
                <++> newline <> stmtsToDoc env (Vector1.toVector stmts)
                <++> exprToDoc env body

        val rec typeOf =
            fn Fn (_, {typ = domain, ...}, arrow, body) =>
                Type.Arrow (arrow, {domain, codomain = typeOf body})
             | TFn (_, params, body) => Type.ForAll (params, typeOf body)
             | EmptyRecord _ => Type.Record Type.EmptyRow
             | With (_, typ, _) => typ
             | Without (_, typ, _) => typ
             | Where (_, typ, _) => typ
             | (App (_, typ, _) | TApp (_, typ, _) | PrimApp (_, typ, _, _, _, _)) => typ
             | Field (_, typ, _, _) => typ
             | Letrec (_, _, body) => typeOf body
             | Let (_, _, body) => typeOf body
             | Match (_, t, _, _) => t
             | Cast (_, t, _, _) => t
             | Type (_, t) => Type.Type t
             | Use (_, {typ, ...}) => typ
             | Const (_, c) => Type.Prim (Const.typeOf c)
    end
end

