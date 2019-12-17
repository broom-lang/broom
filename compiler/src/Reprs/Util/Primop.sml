structure Primop :> sig
    datatype t
        = IntT | IAdd | ISub | IMul | IDiv
        | UIntT | UAdd | USub | UMul | UDiv
        | ArrayT | ArrayNew | ArrayCount | ArrayGet | ArrayUnsafeSet
        | BoxT | BoxNew | BoxGet | BoxInit
        | Panic

    val fromString : string -> t option
    val toDoc : t -> PPrint.t

    val isTotal : t -> bool
end = struct
    datatype t
        = IntT | IAdd | ISub | IMul | IDiv
        | UIntT | UAdd | USub | UMul | UDiv
        | ArrayT | ArrayNew | ArrayCount | ArrayGet | ArrayUnsafeSet
        | BoxT | BoxNew | BoxGet | BoxInit
        | Panic

    val fromString =
        fn "__int" => SOME IntT
         | "__iAdd" => SOME IAdd
         | "__iSub" => SOME ISub
         | "__iMul" => SOME IMul
         | "__iDiv" => SOME IDiv
         | "__uint" => SOME UIntT
         | "__uAdd" => SOME UAdd
         | "__uSub" => SOME USub
         | "__uMul" => SOME UMul
         | "__uDiv" => SOME UDiv
         | "__array" => SOME ArrayT
         | "__arrayNew" => SOME ArrayNew
         | "__arrayCount" => SOME ArrayCount
         | "__arrayGet" => SOME ArrayGet
         | "__arrayUnsafeSet" => SOME ArrayUnsafeSet
         | "__box" => SOME BoxT
         | "__boxNew" => SOME BoxNew
         | "__boxGet" => SOME BoxGet
         | "__boxInit" => SOME BoxInit
         | "__panic" => SOME Panic
         | _ => NONE

    fun toDoc opn =
        PPrint.text ("__" ^ (case opn
            of IntT => "int"
             | IAdd => "iAdd"
             | ISub => "iSub"
             | IMul => "iMul"
             | IDiv => "iDiv"
             | UIntT => "uint"
             | UAdd => "uAdd"
             | USub => "uSub"
             | UMul => "uMul"
             | UDiv => "uDiv"
             | ArrayT => "array"
             | ArrayNew => "arrayNew"
             | ArrayCount => "arrayCount"
             | ArrayGet => "arrayGet"
             | ArrayUnsafeSet => "arrayUnsafeSet"
             | BoxT => "box"
             | BoxNew => "boxNew"
             | BoxGet => "boxGet"
             | BoxInit => "boxInit"
             | Panic => "panic"))

    val isTotal =
        fn IntT => true
         | IAdd | ISub | IMul | IDiv => false
         | UIntT => true
         | UAdd | USub | UMul | UDiv => false
         | ArrayT | ArrayNew | ArrayCount => true
         | ArrayGet | ArrayUnsafeSet => false
         | BoxT | BoxNew | BoxGet | BoxInit => true
         | Panic => false
end

