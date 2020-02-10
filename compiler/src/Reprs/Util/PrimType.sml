signature PRIM_TYPE = sig
    datatype t
        = Bool | Int | UInt
        | Array | Box
        | Layout | SlotMap | StackT
        | VoidPtr

    val toString: t -> string
    val toDoc: t -> PPrint.t
end

structure PrimType :> PRIM_TYPE = struct
    datatype t
        = Bool | Int | UInt
        | Array | Box
        | Layout | SlotMap | StackT
        | VoidPtr
    
    fun toString t =
        "__"
        ^ (case t
           of Bool => "bool"
            | Int => "int"
            | UInt => "uint"
            | Array => "array"
            | Box => "box"
            | Layout => "layout"
            | SlotMap => "slotMap"
            | StackT => "stack"
            | VoidPtr => "voidPtr")

    val toDoc = PPrint.text o toString
end

