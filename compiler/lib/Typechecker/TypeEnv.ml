open Asserts

module T = Fc.Type
type var = Fc.Term.Expr.var
module Tx = Transactional
open Tx.Ref

type error_handler = TypeError.t -> unit

type scope =
    | Vals of var Name.Map.t

type t =
    { scopes : scope list
    ; level : T.level
    ; error_handler : error_handler }

let report_error (env : t) err = env.error_handler err

let with_error_handler (env : t) error_handler = {env with error_handler}

let eval () =
    { scopes = []
    ; level = 1
    ; error_handler = fun err -> unreachable (Some err.pos) }

let push_val (env : t) (var : var) =
    match env.scopes with
    | Vals bindings :: scopes' ->
        {env with scopes = Vals (Name.Map.add var.name var bindings) :: scopes'}
    | scopes ->
        {env with scopes = Vals (Name.Map.singleton var.name var) :: scopes}

let uv env kind = ref (T.Unassigned (Name.fresh (), kind, env.level))

