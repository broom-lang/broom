type t

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val fresh : unit -> t
val of_string : string -> t
val freshen : t -> t

val basename : t -> string option

val to_string : t -> string
val to_doc : t -> PPrint.document

module Map : Map.S with type key = t
module Hashtbl : Hashtbl.S with type key = t

