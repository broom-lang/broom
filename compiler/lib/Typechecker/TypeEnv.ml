open Asserts

module T = Fc.Type
module FExpr = Fc.Term.Expr
type var = FExpr.var
type expr = Fc.Term.Expr.t
module Tx = Transactional
open Tx.Ref

type error_handler = TypeError.t -> unit

type scope =
    | Vals of var Name.Map.t

type t =
    { namespace : Namespace.t
    ; scopes : scope list
    ; level : T.level
    ; error_handler : error_handler }

let report_error (env : t) err = env.error_handler err

let with_error_handler (env : t) error_handler = {env with error_handler}

let toplevel namespace =
    { namespace = namespace
    ; scopes = []
    ; level = 1
    ; error_handler = fun err -> unreachable (Some err.pos) }

let namespace (env : t) = env.namespace

let uv env kind = ref (T.Unassigned (Name.fresh (), kind, env.level))

let push_val is_global (env : t) (var : var) =
    if is_global
    then {env with namespace = Namespace.add env.namespace var}
    else match env.scopes with
        | Vals bindings :: scopes' ->
            {env with scopes = Vals (Name.Map.add var.name var bindings) :: scopes'}
        | scopes ->
            {env with scopes = Vals (Name.Map.singleton var.name var) :: scopes}

let find_val (env : t) span name =
    let rec find = function
        | Vals kvs :: scopes -> (match Name.Map.find_opt name kvs with
            | Some var -> FExpr.at span var.vtyp (FExpr.use var)
            | None -> find scopes)
        | [] ->
            (match Namespace.find_typ env.namespace name with
            | Some {vtyp = typ; plicity = _; name = _} ->
                let namexpr = FExpr.at span (Prim String)
                    (FExpr.const (String (Name.to_string name))) in
                FExpr.primapp GlobalGet (Vector.singleton typ)
                    (FExpr.at span (Tuple (Vector.singleton (T.Prim String)))
                        (FExpr.values [|namexpr|]))
                |> FExpr.at span typ
            | None ->
                report_error env ({v = Unbound name; pos = span});
                (* FIXME: levels: *)
                let kind = T.App {callee = Prim TypeIn; arg = Uv (uv env T.rep)} in
                let typ = T.Uv (uv env kind) in
                FExpr.at span typ (FExpr.use (FExpr.var Explicit name typ))) in
    find env.scopes

