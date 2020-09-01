type 'a with_pos = 'a Util.with_pos

module type EXPR = sig
    type typ
    type stmt

    type t =
        | Values of t with_pos Vector.t
        | Ann of t with_pos * typ with_pos
        | Fn of clause Vector.t
        | Thunk of stmt Vector.t
        | App of t with_pos * t with_pos Vector.t
        | AppSequence of t with_pos Vector1.t
        | PrimApp of Primop.t * t with_pos Vector.t
        | Record of stmt Vector.t
        | Select of t with_pos * Name.t
        | Proxy of typ
        | Var of Name.t
        | Const of Const.t

    and clause =
        { iparams : pat with_pos Vector.t
        ; eparams : pat with_pos Vector.t
        ; body : t with_pos }

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

    val to_doc : t -> PPrint.document
end

module type TERM = sig
    module rec Expr : (EXPR with type stmt = Stmt.t)
    and Stmt : (STMT
        with type expr = Expr.t
        with type pat = Expr.pat)
end

module type TYPE = sig
    type expr
    type stmt
    type pat

    type t =
        | Pi of { idomain : pat with_pos; edomain : pat with_pos; eff : t with_pos
            ; codomain : t with_pos }
        | Record of stmt Vector.t
        | Row of stmt Vector.t
        | Path of expr
        | Prim of Prim.t

    val to_doc : t with_pos -> PPrint.document
end

