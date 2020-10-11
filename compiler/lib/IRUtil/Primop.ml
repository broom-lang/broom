module T = FcType.Type

type t =
    | IAdd | ISub | IMul
    | CellNew | CellInit | CellGet
    | Int
    | Type

let of_string = function
    | "iadd" -> Some IAdd
    | "isub" -> Some ISub
    | "imul" -> Some IMul
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
        | CellNew -> "cellNew"
        | CellInit -> "cellInit"
        | CellGet -> "cellGet"
        | Int -> "int"
        | Type -> "type" in
    name

let to_doc op = PPrint.string (to_string op)

