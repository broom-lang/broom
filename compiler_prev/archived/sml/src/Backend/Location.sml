signature LOCATION = sig
    structure Register : REGISTER

    datatype t
        = Register of Register.t
        | StackSlot of StackSlot.t

    val eq : t * t -> bool
    val compare : t * t -> order
    val toDoc : t -> PPrint.t
    val toString : t -> string

    val isReg : t -> bool
    val isStackSlot : t -> bool

    structure SortedSet : ORD_SET where type Key.ord_key = t
    structure SortedMap : ORD_MAP where type Key.ord_key = t
end

functor Location (Register : REGISTER) :> LOCATION
    where type Register.t = Register.t
= struct
    structure Register = Register

    datatype t
        = Register of Register.t
        | StackSlot of StackSlot.t

    val eq =
        fn (Register reg, Register reg') => Register.eq (reg, reg')
         | (Register _, StackSlot _) => false
         | (StackSlot _, Register _) => false
         | (StackSlot slot, StackSlot slot') => StackSlot.eq (slot, slot')

    val isReg =
        fn Register _ => true
         | StackSlot _ => false

    val isStackSlot =
        fn Register _ => false
         | StackSlot _ => true

    val compare =
        fn (Register reg, Register reg') => Register.compare (reg, reg')
         | (Register _, StackSlot _) => LESS
         | (StackSlot _, Register _) => GREATER
         | (StackSlot slot, StackSlot slot') => StackSlot.compare (slot, slot')

    val toDoc =
        fn Register reg => Register.toDoc reg
         | StackSlot slot => StackSlot.toDoc slot

    val toString =
        fn Register reg => Register.toString reg
         | StackSlot slot => StackSlot.toString slot

    structure Ord = struct
        type ord_key = t
        val compare = compare
    end
    structure SortedSet = BinarySetFn(Ord)
    structure SortedMap = BinaryMapFn(Ord)
end

