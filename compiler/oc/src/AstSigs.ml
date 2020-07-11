type 'a with_pos = 'a Util.with_pos

module type TERM = sig
    type typ
    type pat

    type expr =
        | Fn of clause Vector.t
        | If of expr with_pos * expr with_pos * expr with_pos
        | App of expr with_pos * expr with_pos
        | Seal of expr with_pos * typ with_pos
        | Struct of def Vector.t
        | Select of expr with_pos * Name.t
        | Proxy of typ with_pos
        | Use of Name.t
        | Const of Const.t

    and clause = {pats : pat with_pos Vector.t; body : expr with_pos}

    and stmt =
        | Def of def
        | Expr of expr with_pos

    and def = Util.span * pat with_pos * expr with_pos

    val expr_to_doc : expr -> PPrint.document
    val stmt_to_doc : stmt -> PPrint.document
end

module type PATTERN = sig
    type typ

    type t =
        | Ann of t with_pos * typ with_pos
        | Binder of Name.t
        | Ignore (* "_" *)
        | Const of Const.t
end

module type TYPE = sig
    type expr
    type pat
    type eff

    type t =
        | Pi of pat with_pos Vector.t * eff * t with_pos
        | Sig of Name.t decl Vector.t
        | Path of expr
        | Singleton of expr with_pos
        | Type
        | Prim of Prim.t

    and 'a decl = {name : 'a; typ : t with_pos}

    val to_doc : t -> PPrint.document
end

