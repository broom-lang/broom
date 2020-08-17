type span = Util.span
type 'a with_pos = 'a Ast.with_pos
type typ = FcType.typ
type abs = FcType.abs
type ov = FcType.ov
type coercion = FcType.coercion

type lvalue = {name : Name.t; typ : typ}

type expr
    = Fn of FcType.binding Vector.t * lvalue * expr with_pos
    | App of expr with_pos * typ Vector.t * expr with_pos
    | Letrec of def Vector1.t * expr with_pos
    | LetType of FcType.binding Vector1.t * expr with_pos
    | Axiom of (Name.t * FcType.kind Vector.t * typ * typ) Vector1.t * expr with_pos
    | Cast of expr with_pos * coercion
    | Pack of typ Vector1.t * expr with_pos
    | Unpack of FcType.binding Vector1.t * lvalue * expr with_pos * expr with_pos
    | If of expr with_pos * expr with_pos * expr with_pos
    | Record of field Vector.t
    | Select of expr with_pos * string
    | Proxy of abs 
    | Use of Name.t
    | Const of Const.t
    | Patchable of expr with_pos ref

and def = span * lvalue * expr with_pos

and field = {label : string; expr : expr with_pos}

type stmt
    = Def of def
    | Expr of expr with_pos

val lvalue_to_doc : lvalue -> PPrint.document
val expr_to_doc : expr -> PPrint.document
val def_to_doc : def -> PPrint.document
val stmt_to_doc : stmt -> PPrint.document

(* TODO: Add more of these: *)
val letrec : def Vector.t -> expr with_pos -> expr

