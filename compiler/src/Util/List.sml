signature LIST_BUILDER = sig
    type 'a t

    val new: unit -> 'a t
    val pushBack: 'a t -> 'a -> unit
    val build: 'a t -> 'a list
end

structure List = struct
    open List

    structure Builder :> LIST_BUILDER = struct
        type 'a t = 'a list ref

        fun new () = ref []

        fun pushBack builder v = builder := v :: !builder

        fun build (ref vs) = rev vs
    end
end

