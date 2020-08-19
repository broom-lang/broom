type t = Int | EmptyRow

let to_string = function
    | Int -> "int"
    | EmptyRow -> "(||)"

let to_doc pt = PPrint.string (to_string pt)

let eq pt pt' = match pt with
    | Int ->
        (match pt' with
        | Int -> true
        | _ -> false)
    | EmptyRow ->
        (match pt' with
        | EmptyRow -> true
        | _ -> false)

