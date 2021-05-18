type span = Util.span
type 'a with_pos = 'a Util.with_pos

module type PRIMOP = sig
    type t =
        | Include | Require
        | Let | Module | Interface

        | Pair | Fst | Snd
        | CellNew | CellInit | CellGet
        | Int | String | Type
        | TypeOf
        | Import
        | GlobalSet | GlobalGet

        | IAdd | ISub | IMul | IDiv
        | ILt | ILe | IGt | IGe | IEq

    val of_string : string -> t option
    val to_doc : t -> PPrint.document
end

module type EXPR = sig
    type primop
    type stmt
    type decl

    type t' =
        | Fn of clause Vector.t
        | ImpliFn of clause Vector.t
        | App of t Vector.t
        | PrimApp of primop * t Vector.t
        | PiT of {domain : t; eff : t option; codomain : t}
        | ImpliT of {domain : t; codomain : t}

        | Ann of t * t

        | Tuple of t Vector.t
        | Focus of t * int
        | TupleT of t Vector.t

        | Record of stmt Vector.t
        | Select of t * Name.t
        | RecordT of decl Vector.t

        | VariantT of decl Vector.t

        | RowT of decl Vector.t

        | Var of Name.t
        | Wild of Name.t
        | Const of Const.t
        | PrimT of Prim.t

    and t = t' with_pos

    and clause = {params : t; body : t}

    val to_doc : t -> PPrint.document

    val map_children : (t -> t) -> t -> t
end

module type STMT = sig
    type expr

    type def = Util.span * expr * expr

    type t =
        | Def of Util.span * expr * expr
        | Expr of expr

    val pos : t -> Util.span

    val to_doc : t -> PPrint.document

    val map_child_exprs : (expr -> expr) -> t -> t
end

module type DECL = sig
    type expr

    type t =
        | Def of Util.span * expr * expr
        | Decl of Util.span * expr * expr
        | Type of expr

    val to_doc : t -> PPrint.document

    val pos : t -> Util.span

    val map_child_exprs : (expr -> expr) -> t -> t
end

module type PROGRAM = sig
    module Stmt : STMT
    module Expr : EXPR

    type t = {span : span; defs : Stmt.def Vector.t; body : Expr.t}

    val to_doc : t -> PPrint.document
end

