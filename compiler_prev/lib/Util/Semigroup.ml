module type S = sig
    type t
    val combine : t -> t -> t
end

