module T = Fc.Type
module AExpr = Ast.Term.Expr
type 'a with_pos = 'a Util.with_pos

type t' =
    | NonPattern of AExpr.t with_pos
    | PrimAppArgc of {op : Primop.t; expected : int; actual : int}
    | PrimAppIArgc of {op : Primop.t; expected : int; actual : int}
    | Subtype of T.t * T.t
    | Unify of T.t * T.t
    | Unbound of Name.t
    | Occurs of T.uv * T.t
    | IncompleteImpl of T.uv * T.uv

type t = t' Util.with_pos

val to_doc : t -> PPrint.document

