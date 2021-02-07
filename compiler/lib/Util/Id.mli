module type S = sig
    type t = private int

    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int

    val fresh : unit -> t

    val to_string : t -> string
    val to_doc : t -> PPrint.document
    val grammar : t Grammar.t

    module HashMap : CCHashTrie.S with type key = t
    module Hashtbl : CCHashtbl.S with type key = t
    module HashSet : CCHashSet.S with type elt = t
end

module Make () : S

