signature PRIM_TYPE = sig
    datatype t
        = Bool | Int | UInt
        | Array | Box
        | StackT

    val toString: t -> string
    val toDoc: t -> PPrint.t
end

structure PrimType :> PRIM_TYPE = struct
    datatype t
        = Bool | Int | UInt
        | Array | Box
        | StackT
    
    val toString =
        fn Bool => "Bool"
         | Int => "Int"
         | UInt => "UInt"
         | Array => "Array"
         | Box => "Box"
         | StackT => "Stack"

    val toDoc = PPrint.text o toString
end

