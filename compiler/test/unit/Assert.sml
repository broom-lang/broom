functor Assert (Value : sig
    type t

    val eq : t * t -> bool
    val toString : t -> string
end) :> sig
    exception AssertFailed of string

    val ok : bool -> string -> unit
    val eq : Value.t * Value.t -> string -> unit
end = struct
    exception AssertFailed of string

    fun ok true _ = ()
      | ok false msg = raise AssertFailed msg

    fun eq (vs as (a, b)) msg =
        if Value.eq vs
        then ()
        else raise AssertFailed ( Value.toString a ^ " <> " ^ Value.toString b
                                ^ ": " ^ msg )
end

