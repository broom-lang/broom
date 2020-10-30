module T = FcType.Type

type behaviour = Pure | Impure | Branch

type t =
    | IAdd | ISub | IMul | IDiv
    | ILt | ILe | IGt | IGe | IEq
    | CellNew | CellInit | CellGet
    | Int
    | Type

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
    | "cellNew" -> Some CellNew
    | "cellInit" -> Some CellInit
    | "cellGet" -> Some CellGet
    | "int" -> Some Int
    | "type" -> Some Type
    | _ -> None

let to_string op =
    let name = match op with
        | IAdd -> "iadd"
        | ISub -> "isub"
        | IMul -> "imul"
        | IDiv -> "idiv"
        | ILt -> "ilt"
        | ILe -> "ile"
        | IGt -> "igt"
        | IGe -> "ige"
        | IEq -> "ieq"
        | CellNew -> "cellNew"
        | CellInit -> "cellInit"
        | CellGet -> "cellGet"
        | Int -> "int"
        | Type -> "type" in
    name

let to_doc op = PPrint.string (to_string op)

let behaviour = function
    | CellNew | Int | Type -> Pure
    | CellInit | CellGet -> Impure
    | IAdd | ISub | IMul | IDiv
    | ILt | ILe | IGt | IGe | IEq -> Branch

