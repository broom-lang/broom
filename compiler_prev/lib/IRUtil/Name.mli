include Id.S

val freshen : t -> t
val of_string : string -> t

val basename : t -> string option
val basename_iso : (string, t) PIso.t

module Map : Map.S with type key = t

