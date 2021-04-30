module T = Fc.Type
type var = Fc.Term.Expr.var
type expr = Fc.Term.Expr.t

type t

val empty : t
val toplevel : Namespace.t -> t

val namespace : t -> Namespace.t option
val type_fns : t -> T.def Vector.t

type error_handler = TypeError.t -> unit

val report_error : t -> error_handler
val with_error_handler : t -> error_handler -> t

val push_val : bool -> t -> var -> t
val find_val : t -> Util.span -> Name.t -> expr

val uv : t -> bool -> T.kind -> T.uv

