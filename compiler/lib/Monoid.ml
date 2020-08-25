module type S = sig
    include Semigroup.S

    val empty : t
end

module OfSemigroup (Semi : Semigroup.S) = struct
    type t = Semi.t option

    let empty = None

    let combine a b = match (a, b) with
        | (Some a, Some b) -> Some (Semi.combine a b)
        | (Some _ as c, None) | (None, (Some _ as c)) -> c
        | (None, None) -> empty
end

