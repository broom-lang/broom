type t

val create : unit -> t
val clone : t -> t
val add : t -> Name.t -> Value.t -> unit
val find : t -> Name.t -> Value.t option

