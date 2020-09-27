module type TYPE = FcTypeSigs.TYPE

module type EXPR = sig
    module Type : TYPE

    type def
    type stmt

    type 'a wrapped = {term : 'a; typ : Type.t; pos : Util.span}

    type lvalue = {name : Name.t; typ : Type.t}

    type t =
        | Values of t wrapped Vector.t
        | Focus of t wrapped * int

        | Fn of Type.binding Vector.t * lvalue * t wrapped
        | App of t wrapped * Type.t Vector.t * t wrapped
        | PrimApp of Primop.t * Type.t Vector.t * t wrapped

        | Let of def * t wrapped
        | Letrec of def Vector1.t * t wrapped
        | LetType of Type.binding Vector1.t * t wrapped
        | Match of t wrapped * clause Vector.t

        | Axiom of (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector1.t * t wrapped
        | Cast of t wrapped * Type.coercion

        | Pack of Type.t Vector1.t * t wrapped
        | Unpack of Type.binding Vector1.t * lvalue * t wrapped * t wrapped

        | Record of (Name.t * t wrapped) Vector.t
        | Where of t wrapped * (Name.t * t wrapped) Vector1.t
        | With of {base : t wrapped; label : Name.t; field : t wrapped}
        | Select of t wrapped * Name.t

        | Proxy of Type.t
        | Const of Const.t

        | Use of Name.t

        | Patchable of t wrapped TxRef.rref

    and pat =
        | ValuesP of pat wrapped Vector.t
        | AppP of t wrapped * pat wrapped Vector.t
        | ProxyP of Type.t
        | UseP of Name.t
        | ConstP of Const.t

    and clause = {pat : pat wrapped; body : t wrapped}

    and field = {label : string; expr : t wrapped}

    val lvalue_to_doc : Type.subst -> lvalue -> PPrint.document
    val pat_to_doc : Type.subst -> pat wrapped -> PPrint.document
    val to_doc : Type.subst -> t wrapped -> PPrint.document

    (* TODO: Add more of these: *)
    val letrec : def Vector.t -> t wrapped -> t

    val map_children : (t wrapped -> t wrapped) -> t wrapped -> t wrapped
end

module type STMT = sig
    module Type : TYPE

    type expr
    type pat

    type def = Util.span * pat * expr

    type t
        = Def of def
        | Expr of expr

    val def_to_doc : Type.subst -> def -> PPrint.document
    val to_doc : Type.subst -> t -> PPrint.document

    val rhs : t -> expr
end

module type TERM = sig
    module Type : TYPE

    module rec Expr : (EXPR
        with module Type = Type
        with type def = Stmt.def
        with type stmt = Stmt.t)

    and Stmt : (STMT
        with module Type = Type
        with type expr = Expr.t Expr.wrapped
        with type pat = Expr.pat Expr.wrapped)
end

