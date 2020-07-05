type span = Lexing.position * Lexing.position

val span_to_string : span -> string

type 'a with_pos = {v : 'a; pos: span}

module rec Term : sig
    type expr =
        | Fn of lvalue * expr with_pos
        | If of expr with_pos * expr with_pos * expr with_pos
        | App of expr with_pos * expr with_pos
        | Seal of expr with_pos * Type.t with_pos
        | Struct of def Vector.t
        | Select of expr with_pos * Name.t
        | Proxy of Type.t with_pos
        | Use of Name.t
        | Const of Const.t

    and stmt =
        | Def of def
        | Expr of expr with_pos

    and def = span * lvalue * expr with_pos

    and lvalue = {pat : Name.t; ann: Type.t with_pos option}

    val expr_to_doc : expr -> PPrint.document
    val stmt_to_doc : stmt -> PPrint.document
end

and Type : sig
    type t =
        | Pi of Name.t option decl * Effect.t * t with_pos
        | Sig of Name.t decl Vector.t
        | Path of Term.expr
        | Singleton of Term.expr with_pos
        | Type
        | Prim of Prim.t

    and 'a decl = {name : 'a; typ : t with_pos}

    val to_doc : t -> PPrint.document
end

and Effect : sig
    type t = Pure | Impure

    val to_doc : t -> PPrint.document
    val arrow : t -> PPrint.document
end

