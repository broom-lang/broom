module T = Fc.Type
module AExpr = Ast.Expr
type 'a with_pos = 'a Util.with_pos

type t' =
    | NonPattern of AExpr.t
    | PrimAppArgc of {op : Primop.t; expected : int; actual : int}
    | BranchopArgc of {op : Branchop.t; expected : int; actual : int}
    | BranchopClausec of {op : Branchop.t; expected : int; actual : int}
    | Subtype of T.t * T.t
    | Unify of T.t * T.t
    | Unbound of Name.t
    | Occurs of T.uv * T.t
    | IncompleteImpl of T.uv * T.uv

type t = t' Util.with_pos

val to_doc : t -> PPrint.document

