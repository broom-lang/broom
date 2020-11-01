type span = Util.span

module type TYPE = sig
    type kind = Fc.Type.kind
    type param = Fc.Type.binding

    type t =
        | Values of t Vector.t
        | PromotedValues of t Vector.t
        | PromotedArray of t Vector.t
        | Pi of {universals : kind Vector.t; domain : t Vector.t}
        | Record of t
        | With of {base : t; label : Name.t; field : t}
        | EmptyRow
        | App of t * t
        | Prim of Prim.t

    val to_doc : t -> PPrint.document
    val param_to_doc : param -> PPrint.document
end

module type EXPR = sig
    type cont_id
    module Type : TYPE

    module Id : Id.S

    type t' =
        | PrimApp of {op : Primop.t; universals : Type.t Vector.t; args : Id.t Vector.t}
        | Values of Id.t Vector.t
        | Focus of {focusee : Id.t; index : int}
        | Record of (Name.t * Id.t) Vector.t
        | With of {base : Id.t; label: Name.t; field : Id.t}
        | Where of {base : Id.t; fields : (Name.t * Id.t) Vector.t}
        | Select of {selectee : Id.t; field : Name.t}
        | Proxy of Type.t
        | Label of cont_id
        | Param of {label : cont_id; index : int}
        | Const of Const.t

    type t =
        { pos : span
        ; cont : cont_id option
        ; typ : Type.t
        ; term : t' }

    val to_doc : t -> PPrint.document
    val term_to_doc : t' -> PPrint.document
    val iter_labels : (cont_id -> unit) -> t -> unit
    val iter_labels' : (cont_id -> unit) -> t' -> unit
    val iter_uses' : (Id.t -> unit) -> t' -> unit
    val iter_uses : (Id.t -> unit) -> t -> unit
    val map_uses : (Id.t -> Id.t) -> t' -> t'
end

module type PATTERN = sig
    type t =
        | Const of Const.t
        | Wild

    val to_doc : t -> PPrint.document
end

module type TRANSFER = sig
    module Type : TYPE
    module Pattern : PATTERN
    type expr_id
    type cont_id

    type clause = {pat : Pattern.t; dest : cont_id}

    type t' =
        | Goto of {callee : cont_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Jump of {callee : expr_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Match of {matchee : expr_id; state : expr_id; clauses : clause Vector.t}
        | PrimApp of {op : Primop.t; universals : Type.t Vector.t
            ; state : expr_id; args : expr_id Vector.t; clauses : clause Vector.t}
        | Return of Type.t Vector.t * expr_id Vector.t

    type t = {pos : span; term : t'}

    val to_doc : t -> PPrint.document
    val iter_labels : (cont_id -> unit) -> t -> unit
    val iter_uses : (expr_id -> unit) -> t -> unit
end

module type CONT = sig
    module Type : TYPE
    module Transfer : TRANSFER

    module Id : Id.S

    type t =
        { pos : span
        ; name : Name.t option
        ; universals : Type.param Vector.t
        ; params : Type.t Vector.t
        ; body : Transfer.t }

    val to_doc : t -> exprs_doc: PPrint.document -> PPrint.document
end

module type PROGRAM = sig
    module Type : TYPE
    module Expr : EXPR
    module Cont : CONT

    type t
    type builder

    val to_doc : t -> PPrint.document

    val type_fns : t -> Type.param Vector.t
    val exports : t -> Cont.Id.t Streaming.Source.t
    val cont : t -> Cont.Id.t -> Cont.t
    val expr : t -> Expr.Id.t -> Expr.t
    val exprs : t -> (Expr.Id.t * Expr.t) Streaming.Stream.t

    val usecounts : t -> int Expr.Id.HashMap.t

    module Builder : sig
        val create : Type.param Vector.t -> builder
        val express : builder -> Expr.t -> Expr.Id.t
        val add_cont : builder -> Cont.Id.t -> Cont.t -> unit
        val build : builder -> Cont.Id.t -> t

        type t = builder
    end
end

