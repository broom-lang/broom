structure Primop :> sig
    datatype t
        = IAdd | ISub | IMul | IDiv
        | ArrayNew | ArrayCount | ArrayGet | ArrayUnsafeSet

    val fromString : string -> t option
    val toDoc : t -> PPrint.t
end = struct
    datatype t
        = IAdd | ISub | IMul | IDiv
        | ArrayNew | ArrayCount | ArrayGet | ArrayUnsafeSet

    val fromString =
        fn "__iAdd" => SOME IAdd
         | "__iSub" => SOME ISub
         | "__iMul" => SOME IMul
         | "__iDiv" => SOME IDiv
         | "__arrayNew" => SOME ArrayNew
         | "__arrayCount" => SOME ArrayCount
         | "__arrayGet" => SOME ArrayGet
         | "__arrayUnsafeSet" => SOME ArrayUnsafeSet
         | _ => NONE

    fun toDoc opn =
        PPrint.text ("__" ^ (case opn
            of IAdd => "iAdd"
             | ISub => "iSub"
             | IMul => "iMul"
             | IDiv => "iDiv"
             | ArrayNew => "arrayNew"
             | ArrayCount => "arrayCount"
             | ArrayGet => "arrayGet"
             | ArrayUnsafeSet => "arrayUnsafeSet"))
end

