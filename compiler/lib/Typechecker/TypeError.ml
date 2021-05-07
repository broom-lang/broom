open Asserts

module T = Fc.Type
module AExpr = Ast.Term.Expr
open Transactional.Ref
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

let to_doc (err : t) =
    let open PPrint in

    (match err.v with
    | NonPattern pat ->
        AExpr.to_doc pat ^/^ string "is" ^/^ string "not" ^/^ string "a" ^/^ string "valid"
        ^/^ string "pattern"

    | PrimAppArgc {op; expected; actual} ->
        string "wrong" ^/^ string "number" ^/^ string "of" ^/^ string "arguments"
        ^/^ string "to" ^/^ string "__" ^^ Primop.to_doc op ^^ semi
        ^/^ string "expected" ^^ blank 1 ^^ string (Int.to_string expected) ^^ comma
        ^/^ string "got" ^^ blank 1 ^^ string (Int.to_string actual)
    | PrimAppIArgc {op; expected; actual} ->
        string "wrong" ^/^ string "number" ^/^ string "of" ^/^ string "type" ^/^ string "arguments"
        ^/^ string "to" ^/^ string "__" ^^ Primop.to_doc op ^^ semi
        ^/^ string "expected" ^^ blank 1 ^^ string (Int.to_string expected) ^^ comma
        ^/^ string "got" ^^ blank 1 ^^ string (Int.to_string actual)

    | Subtype (sub, super) ->
        T.to_doc sub ^/^ string "is" ^/^ string "not" ^/^ string "a" ^/^ string "subtype"
        ^/^ string "of" ^/^ T.to_doc super
    | Unify (ltyp, rtyp) ->
        T.to_doc ltyp ^/^ string "does" ^/^ string "not" ^/^ string "unify" ^/^ string "with"
        ^/^ T.to_doc rtyp
    | Unbound name -> infix 4 1 colon (string "unbound" ^/^ string "variable") (Name.to_doc name)
    | Occurs (uv, typ) ->
        (match !uv with
        | Unassigned (_, name, _, _) ->
            string "the" ^/^ string "unification" ^/^ string "variable" ^/^ Name.to_doc name
            ^/^ string "occurs" ^/^ string "in" ^/^ T.to_doc typ
        | Assigned _ -> todo (Some err.pos))
    | IncompleteImpl _ -> todo (Some err.pos))
    |> group

