type t =
    | IAdd | ISub | IMul | IDiv
    | ILt | ILe | IGt | IGe | IEq

let of_string = function
    | "iadd" -> Some IAdd
    | "isub" -> Some ISub
    | "imul" -> Some IMul
    | "idiv" -> Some IDiv
    | "ilt" -> Some ILt
    | "ile" -> Some ILe
    | "igt" -> Some IGt
    | "ige" -> Some IGe
    | "ieq" -> Some IEq
    | _ -> None

let to_string = function
    | IAdd -> "iadd"
    | ISub -> "isub"
    | IMul -> "imul"
    | IDiv -> "idiv"
    | ILt -> "ilt"
    | ILe -> "ile"
    | IGt -> "igt"
    | IGe -> "ige"
    | IEq -> "ieq"

let to_doc op = PPrint.string (to_string op)

