type t

val interactive : unit -> t
val eval : unit -> t

val add : Name.t -> Fc.Type.t -> t -> t
val find : Name.t -> t -> Fc.Type.t

val current_uv_subst : t -> Fc.Uv.subst

