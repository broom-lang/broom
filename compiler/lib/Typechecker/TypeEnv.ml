open Asserts

module T = Fc.Type
module Tx = Transactional
open Tx.Ref

type error_handler = TypeError.t -> unit

type t =
    { level : T.level
    ; error_handler : error_handler }

let report_error (env : t) err = env.error_handler err

let with_error_handler (env : t) error_handler = {env with error_handler}

let eval () = {level = 1; error_handler = fun err -> unreachable (Some err.pos)}

let uv env kind = ref (T.Unassigned (Name.fresh (), kind, env.level))

