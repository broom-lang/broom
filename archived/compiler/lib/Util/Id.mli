module type S = sig
    type t = private int

    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int

    val fresh : unit -> t

    val to_string : t -> string
    val to_doc : t -> PPrint.document
    val grammar : t Grammar.t

    module HashMap : sig
        include CCHashTrie.S with type key = t

        val to_source : 'a t -> (key * 'a) Streaming.Source.t
    end

    module Hashtbl : Hashtbl.S with type key = t
    module HashSet : CCHashSet.S with type elt = t
end

module Make () : S

