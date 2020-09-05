module T = Fc.Type

type uv = Fc.Uv.t

type t

val interactive : unit -> t
val eval : unit -> t

val find : t -> Util.span -> Name.t -> Fc.Type.t

val push_val : t -> Name.t -> T.t -> t
val push_existential : t -> t * T.ov list TxRef.rref
val push_skolems : t -> T.kind Vector.t -> t * T.ov Vector.t
val push_axioms : t -> (Name.t * T.ov * uv) Vector1.t -> t

val generate : t -> T.binding -> T.binding * T.level

val get_implementation : t -> T.ov -> (Name.t * T.ov * uv) option

(* HACK: *)
val uv : t -> Name.t -> uv
val sibling : t -> uv -> uv
val get_uv : t -> uv -> Fc.Uv.v
val set_uv : t -> uv -> Fc.Uv.v -> unit

val tx_log : t -> TxRef.log

