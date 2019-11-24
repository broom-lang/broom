structure Primop :> sig
    datatype t = IAdd | ISub | IMul | IDiv

    val fromString : string -> t option
    val toDoc : t -> PPrint.t
end = struct
    datatype t = IAdd | ISub | IMul | IDiv

    val fromString =
        fn "__iAdd" => SOME IAdd
         | "__iSub" => SOME ISub
         | "__iMul" => SOME IMul
         | "__iDiv" => SOME IDiv
         | _ => NONE

    fun toDoc opn =
        PPrint.text ("__" ^ (case opn
            of IAdd => "iAdd"
             | ISub => "iSub"
             | IMul => "iMul"
             | IDiv => "iDiv"))
end

