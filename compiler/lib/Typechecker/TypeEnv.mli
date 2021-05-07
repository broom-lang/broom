module T = Fc.Type
module FExpr = Fc.Term.Expr
type span = Util.span
type 'a with_pos = 'a Util.with_pos

type t

val empty : t
val toplevel : Namespace.t -> t

val namespace : t -> Namespace.t option
val type_fns : t -> T.def Vector.t

type error_handler = TypeError.t -> unit

val report_error : t -> error_handler
val with_error_handler : t -> error_handler -> t

val push_val : bool -> t -> FExpr.var -> t
val find_val : (t -> Ast.Type.t with_pos -> T.t * T.kind)
    -> (span -> t -> T.t -> T.t -> unit)
    -> t -> span -> Name.t -> FExpr.t
val implicits : t -> FExpr.var Streaming.Stream.t

val push_row : t -> (FExpr.var Vector.t * T.t * Ast.Type.t Util.with_pos) CCVector.ro_vector -> t
val force_typ : (t -> Ast.Type.t with_pos -> T.t * T.kind)
    -> (span -> t -> T.t -> T.t -> unit)
    -> t -> span -> Name.t -> unit

val push_existential : t -> t * T.ov list Transactional.Ref.t
val generate : t -> T.def -> T.ov
val reabstract : t -> T.t -> T.ov Vector.t * T.t

val push_abs_skolems : t -> T.kind Vector1.t -> T.t -> t * T.ov Vector1.t * T.t
val instantiate_abs : t -> T.kind Vector1.t -> T.t -> T.uv Vector1.t * T.t

val push_arrow_skolems : t -> T.kind Vector.t -> T.t -> T.t -> T.t
    -> t * T.ov Vector.t * T.t * T.t * T.t
val instantiate_arrow : t -> T.kind Vector.t -> T.t -> T.t -> T.t
    -> T.uv Vector.t * T.t * T.t * T.t

val push_impli_skolems : t -> T.kind Vector.t -> T.t -> T.t
    -> t * T.ov Vector.t * T.t * T.t
val instantiate_impli : t -> T.kind Vector.t -> T.t -> T.t
    -> T.uv Vector.t * T.t * T.t

val instantiate_primop : t -> T.kind Vector.t -> T.t Vector.t -> T.t -> T.t
    -> T.uv Vector.t * T.t Vector.t * T.t * T.t
val instantiate_branch : t -> T.kind Vector.t -> T.t Vector.t -> T.t -> T.t Vector.t
    -> T.uv Vector.t * T.t Vector.t * T.t * T.t Vector.t

val uv : t -> bool -> T.kind -> T.uv
val some_type_kind : t -> bool -> T.t

