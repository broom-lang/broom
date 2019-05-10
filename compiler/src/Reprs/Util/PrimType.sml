signature PRIM_TYPE = sig
    datatype t = Unit | I32

    val toString: t -> string
end

structure PrimType :> PRIM_TYPE = struct
    datatype t = Unit | I32
    
    val toString = fn Unit => "()"
                    | I32 => "I32"
end

