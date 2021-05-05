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

val push_existential : t -> t * T.ov list Transactional.Ref.t
val generate : t -> T.def -> T.ov
val reabstract : t -> T.t -> T.ov Vector.t * T.t

val push_abs_skolems : t -> T.kind Vector1.t -> T.t -> t * T.ov Vector1.t * T.t
val instantiate_abs : t -> T.kind Vector1.t -> T.t -> T.uv Vector1.t * T.t

val push_arrow_skolems : t -> T.kind Vector.t -> T.t -> T.t -> T.t
    -> t * T.ov Vector.t * T.t * T.t * T.t
val instantiate_arrow : t -> T.kind Vector.t -> T.t -> T.t -> T.t
    -> T.uv Vector.t * T.t * T.t * T.t

val uv : t -> bool -> T.kind -> T.uv
val some_type_kind : t -> bool -> T.t

