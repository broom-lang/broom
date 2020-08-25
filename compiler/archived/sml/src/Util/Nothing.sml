(* A type with no values. *)
signature NOTHING = sig
    type t

    val toString: t -> string
end

structure Nothing :> NOTHING = struct
    type t = unit

    fun toString _ = raise Fail "unreachable"
end

