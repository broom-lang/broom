module T = Fc.Type
type var = Fc.Term.Expr.var

type t

val eval : unit -> t

type error_handler = TypeError.t -> unit

val report_error : t -> error_handler
val with_error_handler : t -> error_handler -> t

val push_val : t -> var -> t
val find_val : t -> Util.span -> Name.t -> var

val uv : t -> T.kind -> T.uv

