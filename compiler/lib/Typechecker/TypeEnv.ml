open Asserts

type error_handler = TypeError.t -> unit

type t =
    { error_handler : error_handler }

let report_error (env : t) err = env.error_handler err

let with_error_handler (_ : t) error_handler = {error_handler}

let eval () = {error_handler = fun err -> unreachable (Some err.pos)}

