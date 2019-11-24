structure Primop :> sig
    datatype t = IAdd | ISub | IMul | IDiv

    val fromString : string -> t option
    val toDoc : t -> PPrint.t

    val typeOf : t -> {domain: PrimType.t vector, codomain: PrimType.t}
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

    val typeOf =
        fn IAdd | ISub | IMul | IDiv =>
            {domain = #[PrimType.I32, PrimType.I32], codomain = PrimType.I32}
end

