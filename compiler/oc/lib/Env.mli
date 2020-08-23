type t

val interactive : unit -> t
val eval : unit -> t

val add : Name.t -> Fc.Type.t -> t -> t
val find : Name.t -> t -> Fc.Type.t

(* HACK: *)
val get_uv : t -> Fc.Uv.t -> Fc.Uv.v
val set_uv : t -> Fc.Uv.t -> Fc.Uv.v -> unit

val current_uv_subst : t -> Fc.Uv.subst
val uv_substr : t -> Fc.Uv.subst ref (* HACK *)

