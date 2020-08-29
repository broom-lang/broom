type 'a with_pos = 'a Util.with_pos

module type TYPE = FcTypeSigs.TYPE

module type EXPR = sig
    module Type : TYPE

    type def
    type stmt

    type lvalue = {name : Name.t; typ : Type.t}

    type t
        = Fn of Type.binding Vector.t * lvalue Vector.t * t with_pos
        | App of t with_pos * Type.t Vector.t * t with_pos Vector.t
        | PrimApp of Primop.t * Type.t Vector.t * t with_pos Vector.t
        | Let of def * t with_pos
        | Letrec of def Vector1.t * t with_pos
        | LetType of Type.binding Vector1.t * t with_pos
        | Match of t with_pos Vector.t * clause Vector.t
        | Axiom of (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector1.t * t with_pos
        | Cast of t with_pos * Type.coercion
        | Pack of Type.t Vector1.t * t with_pos
        | Unpack of Type.binding Vector1.t * lvalue * t with_pos * t with_pos
        | Record of field Vector.t
        | Select of t with_pos * string
        | Proxy of Type.abs 
        | Use of Name.t
        | Const of Const.t
        | Patchable of t with_pos ref

    and clause = {pats : lvalue Vector.t; body : t with_pos}

    and field = {label : string; expr : t with_pos}

    val lvalue_to_doc : Type.subst -> lvalue -> PPrint.document
    val to_doc : Type.subst -> t with_pos -> PPrint.document

    (* TODO: Add more of these: *)
    val letrec : def Vector.t -> t with_pos -> t
end

module type STMT = sig
    module Type : TYPE

    type lvalue
    type expr

    type def = Util.span * lvalue * expr with_pos

    type t
        = Def of def
        | Expr of expr with_pos

    val def_to_doc : Type.subst -> def -> PPrint.document
    val to_doc : Type.subst -> t -> PPrint.document
end

module type TERM = sig
    module Type : TYPE

    module rec Expr : (EXPR
        with module Type = Type
        with type def = Stmt.def
        with type stmt = Stmt.t)

    and Stmt : (STMT
        with module Type = Type
        with type expr = Expr.t
        with type lvalue = Expr.lvalue)
end

