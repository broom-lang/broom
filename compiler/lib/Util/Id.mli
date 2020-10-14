module type S = sig
    type t

    val fresh : unit -> t
    val equal : t -> t -> bool

    val to_doc : t -> PPrint.document

    module HashMap : CCHashTrie.S with type key = t
    module Hashtbl : Hashtbl.S with type key = t
end

module Make () : S

