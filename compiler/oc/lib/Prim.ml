type t = Int | Bool | EmptyRow

let to_string = function
    | Int -> "int"
    | Bool -> "bool"
    | EmptyRow -> "(||)"

let to_doc pt = PPrint.string (to_string pt)

let eq pt pt' = match pt with
    | Int ->
        (match pt' with
        | Int -> true
        | _ -> false)
    | Bool ->
        (match pt' with
        | Bool -> true
        | _ -> false)
    | EmptyRow ->
        (match pt' with
        | EmptyRow -> true
        | _ -> false)

