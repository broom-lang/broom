structure CallingConvention :> sig
    datatype t = CCall

    val toDoc : t -> PPrint.t
end = struct
    val text = PPrint.text

    datatype t = CCall

    val toDoc =
        fn CCall => text "ccall"
end

