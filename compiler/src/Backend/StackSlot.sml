structure StackSlot :> sig
    type t

    val eq : t * t -> bool
    val compare : t * t -> order
    val index : t -> int
    val toDoc : t -> PPrint.t
    val toString : t -> string

    structure SortedMap : ORD_MAP where type Key.ord_key = t

    structure Pool : sig    
        type item = t
        type t

        val empty : int ref -> t
        val allocate : t -> t * item
        val free : t -> item -> t
    end
end = struct
    type t = int

    val eq = op=

    val compare = Int.compare

    val index = Fn.identity

    fun toString i = "sp[" ^ Int.toString i ^ "]"

    val toDoc = PPrint.text o toString

    structure SortedMap = BinaryMapFn(struct
        type ord_key = t
        val compare = compare
    end)

    structure Pool = struct
        type item = t

        type t = {reusables : item list, created : int, maxSlotCount : int ref}

        fun empty maxSlotCount = {reusables = [], created = 0, maxSlotCount}

        fun allocate {reusables, created, maxSlotCount} =
            case reusables
            of x :: reusables => ({reusables, created, maxSlotCount}, x)
             | [] =>
                let val created' = created + 1
                    do maxSlotCount := Int.max (!maxSlotCount, created')
                in ({reusables, created = created', maxSlotCount}, created)
                end

        fun free {reusables, created, maxSlotCount} x =
            {reusables = x :: reusables, created, maxSlotCount}
    end
end

