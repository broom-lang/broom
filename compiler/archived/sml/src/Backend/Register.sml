signature REGISTER = sig
    type t

    val toString : t -> string
    val toDoc : t -> PPrint.t
    val eq : t * t -> bool
    val compare : t * t -> order

    structure SortedMap : ORD_MAP where type Key.ord_key = t
end

