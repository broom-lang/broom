signature PRIM_TYPE = sig
    datatype t = Bool | I32

    val toString: t -> string
    val toDoc: t -> PPrint.t
end

structure PrimType :> PRIM_TYPE = struct
    (* TODO: Replace `Unit` with empty record and remove from here: *)
    datatype t = Bool | I32
    
    val toString = fn Bool => "Bool"
                    | I32 => "I32"

    val toDoc = PPrint.text o toString
end

