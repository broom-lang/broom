type t

val interactive : unit -> t
val eval : unit -> t

val add : Name.t -> FcType.t -> t -> t
val find : Name.t -> t -> FcType.t

val current_uv_subst : t -> FcType.uvv FcType.Uv.store

