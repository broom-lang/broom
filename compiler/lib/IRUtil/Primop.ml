type t =
    | CellNew | CellInit | CellGet
    | Int
    | Type

let of_string = function
    | "cellNew" -> Some CellNew
    | "cellInit" -> Some CellInit
    | "cellGet" -> Some CellGet
    | "int" -> Some Int
    | "type" -> Some Type
    | _ -> None

let to_string = function
    | CellNew -> "cellNew"
    | CellInit -> "cellInit"
    | CellGet -> "cellGet"
    | Int -> "int"
    | Type -> "type"

let to_doc op = PPrint.string (to_string op)

let is_pure = function
    | CellNew | Int | Type -> true
    | CellInit | CellGet -> false

