module T = Fc.Type

type uv = Fc.Uv.t

type t

val interactive : unit -> t
val eval : unit -> t

val add : Name.t -> Fc.Type.t -> t -> t
val find : Name.t -> t -> Fc.Type.t

val push_existential : t -> t * T.binding list ref

val generate : t -> T.binding -> T.binding * T.level

val get_implementation : t -> T.ov -> (Name.t * T.ov * uv) option

(* HACK: *)
val uv : t -> Name.t -> uv
val sibling : t -> uv -> uv
val get_uv : t -> uv -> Fc.Uv.v
val set_uv : t -> uv -> Fc.Uv.v -> unit

val current_uv_subst : t -> Fc.Uv.subst
val uv_substr : t -> Fc.Uv.subst ref (* HACK *)

