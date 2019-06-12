signature SVAR = sig
    type t

    val eq: t * t -> bool
    val toDoc: t -> PPrint.t
end
