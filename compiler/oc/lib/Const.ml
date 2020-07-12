type t =
    | Int of int
    | Bool of bool

let to_doc = function
    | Int n -> PPrint.string (Int.to_string n)
    | Bool b -> PPrint.string (Bool.to_string b)

