type t =
    | CellNew | CellInit | CellGet
    | Int | String | Type
    | TypeOf (* TODO: get rid of this? *)
    | Import
    | GlobalSet | GlobalGet

let of_string = function
    | "cellNew" -> Some CellNew
    | "cellInit" -> Some CellInit
    | "cellGet" -> Some CellGet
    | "int" -> Some Int
    | "string" -> Some String
    | "type" -> Some Type
    | "typeOf" -> Some TypeOf
    | "import" -> Some Import
    | "globalSet" -> Some GlobalSet
    | "globalGet" -> Some GlobalGet
    | _ -> None

let to_string = function
    | CellNew -> "cellNew"
    | CellInit -> "cellInit"
    | CellGet -> "cellGet"
    | Int -> "int"
    | String -> "string"
    | Type -> "type"
    | TypeOf -> "typeOf"
    | Import -> "import"
    | GlobalSet -> "globalSet"
    | GlobalGet -> "globalGet"

let to_doc op = PPrint.string (to_string op)

let is_pure = function
    | CellNew | Int | String | Type | TypeOf -> true
    | CellInit | CellGet | Import (* ? *) | GlobalSet | GlobalGet -> false

