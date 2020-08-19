type t = Int of int

let to_doc = function
    | Int n -> PPrint.string (Int.to_string n)

