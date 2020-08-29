type t = Int

let to_string = function
    | Int -> "int"

let to_doc pt = PPrint.string (to_string pt)

let eq pt pt' = match pt with
    | Int ->
        (match pt' with
        | Int -> true)

