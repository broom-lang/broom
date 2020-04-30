type span = Lexing.position * Lexing.position

type 'a with_pos = {v : 'a; pos: span}

type domain = {name : Name.t option; typ : typ with_pos}

and lvalue = {pat : Name.t; ann: typ with_pos option}

and effect = Pure | Impure

and typ
    = Pi of domain * effect * typ with_pos
    | Sig of decl list
    | Path of expr
    | Singleton of expr with_pos
    | Type
    | Int
    | Bool

and decl = {name : Name.t; typ : typ with_pos}

and expr
    = Fn of lvalue * expr with_pos
    | If of expr with_pos * expr with_pos * expr with_pos
    | App of expr with_pos * expr with_pos
    | Seal of expr with_pos * typ with_pos
    | Struct of def list
    | Select of expr with_pos * Name.t
    | Proxy of typ
    | Use of Name.t
    | Const of int

and def = span * lvalue * expr with_pos

and stmt
    = Def of def
    | Expr of expr with_pos

val effect_to_doc : effect -> PPrint.document
val effect_arrow : effect -> PPrint.document
val def_to_doc : def -> PPrint.document
val typ_to_doc : typ -> PPrint.document
val decl_to_doc : decl -> PPrint.document
val expr_to_doc : expr -> PPrint.document
val stmt_to_doc : stmt -> PPrint.document

