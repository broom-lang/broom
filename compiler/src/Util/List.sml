signature LIST_BUILDER = sig
    type 'a t

    val new: unit -> 'a t
    val pushBack: 'a t -> 'a -> unit
    val build: 'a t -> 'a list
end

structure List = struct
    open List

    fun toString elemToString xs =
        let fun step (x, acc) = acc ^ ", " ^ elemToString x
        in "[" ^
           (case xs
            of x :: xs => foldl step (elemToString x) xs
             | [] => "") ^ "]"
        end

    structure Builder :> LIST_BUILDER = struct
        type 'a t = 'a list ref

        fun new () = ref []

        fun pushBack builder v = builder := v :: !builder

        fun build (ref vs) = rev vs
    end
end

