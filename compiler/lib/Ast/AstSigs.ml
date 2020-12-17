type 'a with_pos = 'a Util.with_pos

module type EXPR = sig
    type typ
    type stmt
    type def

    type t =
        | Tuple of t with_pos Vector.t
        | Focus of t with_pos * int
        | Ann of t with_pos * typ with_pos
        | Fn of clause Vector.t
        | App of t with_pos * (t with_pos, t with_pos) Ior.t
        | AppSequence of t with_pos Vector1.t
        | PrimApp of Primop.t * (t with_pos, t with_pos) Ior.t
        | PrimBranch of Branchop.t * (t with_pos, t with_pos) Ior.t * clause Vector.t
        | Let of def Vector1.t * t with_pos
        | Record of stmt Vector.t
        | Select of t with_pos * Name.t
        | Proxy of typ
        | Var of Name.t
        | Wild of Name.t
        | Const of Const.t

    and clause = {params : (pat with_pos, pat with_pos) Ior.t; body : t with_pos}

    and pat = t

    val to_doc : t with_pos -> PPrint.document
end

module type STMT = sig
    type expr
    type pat

    type def = Util.span * pat with_pos * expr with_pos

    type t =
        | Def of def
        | Expr of expr with_pos

    val pos : t -> Util.span

    val def_to_doc : def -> PPrint.document
    val to_doc : t -> PPrint.document
end

module type TERM = sig
    module rec Expr : (EXPR
        with type stmt = Stmt.t
        with type def = Stmt.def)
    and Stmt : (STMT
        with type expr = Expr.t
        with type pat = Expr.pat)
end

module type TYPE = sig
    type expr
    type stmt
    type pat

    type t =
        | Tuple of t with_pos Vector.t
        | Pi of {domain : (pat with_pos, pat with_pos * t with_pos option) Ior.t; codomain : t with_pos}
        | Record of stmt Vector.t
        | Row of stmt Vector.t
        | Path of expr
        | Prim of Prim.t

    val to_doc : t with_pos -> PPrint.document
end

