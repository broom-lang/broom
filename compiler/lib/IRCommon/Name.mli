include Id.S

val freshen : t -> t
(* FIXME: naming (of_string takes basename, parse is the reverse of to_string: *)
val of_string : string -> t
val parse : string -> t option

val basename : t -> string option
val basename_iso : (string, t) PIso.t

module Map : Map.S with type key = t

