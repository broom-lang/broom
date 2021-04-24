module T = Fc.Type

type t

val eval : unit -> t

type error_handler = TypeError.t -> unit

val report_error : t -> error_handler
val with_error_handler : t -> error_handler -> t

val uv : t -> T.kind -> T.uv

