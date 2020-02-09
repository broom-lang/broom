signature PRIM_TYPE = sig
    datatype t
        = Bool | Int | UInt
        | Array | Box
        | Layout | SlotMap | StackT

    val toString: t -> string
    val toDoc: t -> PPrint.t
end

structure PrimType :> PRIM_TYPE = struct
    datatype t
        = Bool | Int | UInt
        | Array | Box
        | Layout | SlotMap | StackT
    
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
            | StackT => "stack")

    val toDoc = PPrint.text o toString
end

