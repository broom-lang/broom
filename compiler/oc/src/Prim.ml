type t = Int | Bool

let to_string pt =
    "__" ^
    (match pt with
    | Int -> "int"
    | Bool -> "bool")

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

