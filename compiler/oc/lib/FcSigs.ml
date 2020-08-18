type 'a with_pos = 'a Util.with_pos
type typ = FcType.t
type abs = FcType.abs
type coercion = FcType.coercion

module type EXPR = sig
    type def
    type stmt

    type lvalue = {name : Name.t; typ : typ}

    type t
        = Fn of FcType.binding Vector.t * lvalue Vector.t * t with_pos
        | App of t with_pos * typ Vector.t * t with_pos Vector.t
        | Let of def * t with_pos
        | Letrec of def Vector1.t * t with_pos
        | LetType of FcType.binding Vector1.t * t with_pos
        | Axiom of (Name.t * FcType.kind Vector.t * typ * typ) Vector1.t * t with_pos
        | Cast of t with_pos * coercion
        | Pack of typ Vector1.t * t with_pos
        | Unpack of FcType.binding Vector1.t * lvalue * t with_pos * t with_pos
        | If of t with_pos * t with_pos * t with_pos
        | Record of field Vector.t
        | Select of t with_pos * string
        | Proxy of abs 
        | Use of Name.t
        | Const of Const.t
        | Patchable of t with_pos ref

    and field = {label : string; expr : t with_pos}

    val lvalue_to_doc : lvalue -> PPrint.document
    val to_doc : t with_pos -> PPrint.document

    (* TODO: Add more of these: *)
    val letrec : def Vector.t -> t with_pos -> t
end

module type STMT = sig
    type lvalue
    type expr

    type def = Util.span * lvalue * expr with_pos

    type t
        = Def of def
        | Expr of expr with_pos

    val def_to_doc : def -> PPrint.document
    val to_doc : t -> PPrint.document
end

