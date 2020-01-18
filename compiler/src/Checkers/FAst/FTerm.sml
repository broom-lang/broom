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

