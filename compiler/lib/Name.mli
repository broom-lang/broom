type t

val of_string : string -> t
val to_string : t -> string
val compare : t -> t -> int
val fresh : unit -> t
val freshen : t -> t
val to_doc : t -> PPrint.document

module Map : Map.S with type key = t
module Hashtbl : Hashtbl.S with type key = t

