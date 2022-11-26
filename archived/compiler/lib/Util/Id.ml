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

module Make () = struct
    module Key = struct
        type t = int

        let equal = (=)
        let compare = Int.compare
        let hash = Hashtbl.hash
    end

    include Key

    let fresh =
        let counter = ref 0 in
        fun () ->
            let i = !counter in
            counter := i + 1;
            i

    let grammar = Grammar.int

    let to_string = Int.to_string
    let to_doc id = PPrint.string (to_string id)

    module HashMap = struct
        include CCHashTrie.Make (Key)

        let to_source kvs =
            let gen = to_gen kvs in
            Streaming.Source.unfold () (fun () ->
                gen ()
                |> Option.map (fun v -> (v, ()))
            )
    end

    module Hashtbl = Hashtbl.Make (Key)
    module HashSet = CCHashSet.Make (Key)
end

