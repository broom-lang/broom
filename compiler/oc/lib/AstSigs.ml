type 'a with_pos = 'a Util.with_pos

module type TERM = sig
    type typ

    type expr =
        | Values of expr with_pos Vector.t
        | Ann of expr with_pos * typ with_pos
        | Fn of clause Vector.t
        | Thunk of stmt Vector.t
        | App of expr with_pos * expr with_pos Vector.t
        | AppSequence of expr with_pos Vector1.t
        | PrimApp of Primop.t * expr with_pos Vector.t
        | Record of stmt Vector.t
        | Select of expr with_pos * Name.t
        | Proxy of typ
        | Use of Name.t
        | Const of Const.t

    and clause = {pats : pat with_pos Vector.t; body : expr with_pos}

    and stmt =
        | Def of def
        | Expr of expr with_pos

    and def = Util.span * expr with_pos * expr with_pos

    and pat = expr

    val expr_to_doc : expr -> PPrint.document
    val stmt_to_doc : stmt -> PPrint.document
end

module type TYPE = sig
    type expr
    type pat

    type t =
        | Pi of pat with_pos * t with_pos * t with_pos
        | EmptyRow
        | Path of expr
        | Prim of Prim.t

    and 'a decl = {name : 'a; typ : t with_pos}

    val to_doc : t -> PPrint.document
end

