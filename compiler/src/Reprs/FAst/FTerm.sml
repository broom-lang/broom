signature FAST_TERM = sig
    structure Type: CLOSED_FAST_TYPE
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
        | ConstP of Pos.span * Const.t

    withtype clause = {pattern: pat, body: expr}

    type program = { typeFns: Type.def vector
                   , stmts: stmt vector
                   , sourcemap: Pos.sourcemap }
   
    val updateDefTyp : {pos: Pos.span, id: DefId.t, var: Name.t, typ: 't} -> ('t -> 'u)
                     -> {pos: Pos.span, id: DefId.t, var: Name.t, typ: 'u}
    val setDefTyp : {pos: Pos.span, id: DefId.t, var: Name.t, typ: 't} -> 'u
                  -> {pos: Pos.span, id: DefId.t, var: Name.t, typ: 'u}
    val defToDoc : ('expr, 'error) env -> def -> PPrint.t
    val exprPos: expr -> Pos.span
    val exprToDoc: ('expr, 'error) env -> expr -> PPrint.t
    val exprToString: ('expr, 'error) env -> expr -> string
    val stmtPos: stmt -> Pos.span
    val stmtToDoc: ('expr, 'error) env -> stmt -> PPrint.t
    val stmtsToDoc: ('expr, 'error) env -> stmt vector -> PPrint.t
    val patPos: pat -> Pos.span
    val patternToDoc: ('expr, 'error) env -> pat -> PPrint.t
    val programToDoc: ('expr, 'error) env -> program -> PPrint.t
    val typeOf: expr -> Type.concr
end

functor FTerm (Type: CLOSED_FAST_TYPE) :> FAST_TERM
    where type ('expr, 'error) env = ('expr, 'error) Type.env
    where type Type.sv = Type.sv
= struct
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
         | PrimApp (pos, _, _, _, _) => pos
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
                   , stmts: stmt vector
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
        | PrimApp (_, _, opn, targs, args) =>
           parens (Primop.toDoc opn
                   <+> brackets (punctuate (text "," <> space) (Vector.map (Type.Concr.toDoc env) targs))
                   <+> punctuate space (Vector.map (exprToDoc env) args))
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
        | Match (_, _, matchee, clauses) => let
               fun clauseToDoc {pattern, body} =
                   patternToDoc env pattern <+> text "->" <+> exprToDoc env body
               in text "match" <+> exprToDoc env matchee
                  <+> braces (newline <> PPrint.punctuate newline (Vector.map clauseToDoc clauses))
           end
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

    and patternToDoc env =
        fn Def (_, def) => defToDoc env def
         | ConstP (_, c) => Const.toDoc c

    fun exprToString env = PPrint.pretty 80 o exprToDoc env

    val stmtPos =
        fn Val (pos, _, _) => pos
         | Axiom (pos, _, _, _) => pos
         | Expr expr => exprPos expr

    val patPos =
        fn Def (pos, _) => pos
         | ConstP (pos, _) => pos

    fun typeFnToDoc def = text "type" <+> Type.defToDoc def

    fun axiomToDoc env (name, l, r) =
        text "axiom" <+> Name.toDoc name <> text ":"
            <+> Type.Concr.toDoc env l <+> text "~" <+> Type.Concr.toDoc env r

    fun programToDoc env {typeFns, stmts, sourcemap = _} =
        punctuate (newline <> newline) (Vector.map typeFnToDoc typeFns)
            <++> newline <> stmtsToDoc env stmts

    val rec typeOf =
        fn Fn (_, {typ = domain, ...}, arrow, body) =>
            Type.Arrow (arrow, {domain, codomain = typeOf body})
         | TFn (_, params, body) => Type.ForAll (params, typeOf body)
         | EmptyRecord _ => Type.Record Type.EmptyRow
         | With (_, typ, _) => typ
         | Without (_, typ, _) => typ
         | Where (_, typ, _) => typ
         | App (_, typ, _) | TApp (_, typ, _) | PrimApp (_, typ, _, _, _) => typ
         | Field (_, typ, _, _) => typ
         | Letrec (_, _, body) => typeOf body
         | Let (_, _, body) => typeOf body
         | Match (_, t, _, _) => t
         | Cast (_, t, _, _) => t
         | Type (_, t) => Type.Type t
         | Use (_, {typ, ...}) => typ
         | Const (_, c) => Type.Prim (Const.typeOf c)
end

