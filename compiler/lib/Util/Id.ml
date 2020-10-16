module type S = sig
    type t = private int

    val fresh : unit -> t
    val equal : t -> t -> bool

    val to_string : t -> string
    val to_doc : t -> PPrint.document

    module HashMap : CCHashTrie.S with type key = t
    module Hashtbl : Hashtbl.S with type key = t
    module HashSet : CCHashSet.S with type elt = t
end

module Make () = struct
    module Hashable = struct
        type t = int

        let equal = (=)
        let hash = Hashtbl.hash
    end

    include Hashable

    let fresh =
        let counter = ref 0 in
        fun () ->
            let i = !counter in
            counter := i + 1;
            i

    let to_string = Int.to_string
    let to_doc id = PPrint.string (to_string id)

    module HashMap = CCHashTrie.Make (Hashable)
    module Hashtbl = Hashtbl.Make (Hashable)
    module HashSet = CCHashSet.Make (Hashable)
end

