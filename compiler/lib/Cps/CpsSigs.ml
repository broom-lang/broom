type span = Util.span

module type TYPE = sig
    type kind = Fc.Type.kind
    type param = Fc.Type.binding

    type t =
        | Values of t Vector.t
        | PromotedValues of t Vector.t
        | PromotedArray of t Vector.t
        | Pi of {universals : kind Vector.t; domain : t Vector.t}
        | EmptyRow
        | Prim of Prim.t

    val to_doc : t -> PPrint.document
end

module type EXPR = sig
    type cont_id
    module Type : TYPE

    module Id : Id.S

    type t' =
        | Values of Id.t Vector.t
        | Focus of {focusee : Id.t; index : int}
        | Label of cont_id
        | Param of {label : cont_id; index : int}
        | Const of Const.t

    type t =
        { pos : span
        ; cont : cont_id option
        ; typ : Type.t
        ; term : t' }

    val to_doc : t -> PPrint.document
end

module type TRANSFER = sig
    module Type : TYPE
    type expr_id
    type cont_id

    type t' =
        | Goto of {callee : cont_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Jump of {callee : expr_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Return of Type.t Vector.t * expr_id Vector.t

    type t = {pos : span; term : t'}

    val to_doc : t -> PPrint.document
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

    module Builder : sig
        val create : Fc.Type.binding Vector.t -> builder
        val express : builder -> Expr.t -> Expr.Id.t
        val add_cont : builder -> Cont.Id.t -> Cont.t -> unit
        val build : builder -> Cont.Id.t -> t

        type t = builder
    end
end

