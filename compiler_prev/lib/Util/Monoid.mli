module type S = sig
    include Semigroup.S

    val empty : t
end

module OfSemigroup : functor (Semi : Semigroup.S) -> S with type t = Semi.t option

