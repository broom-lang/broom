signature PRIM_TYPE = sig
    datatype t
        = Bool | I32 
        | Array

    val toString: t -> string
    val toDoc: t -> PPrint.t
end

structure PrimType :> PRIM_TYPE = struct
    datatype t
        = Bool | I32
        | Array
    
    val toString =
        fn Bool => "Bool"
         | I32 => "I32"
         | Array => "Array"

    val toDoc = PPrint.text o toString
end

