type t =
    | Int
    | Type | Row

let to_string = function
    | Int -> "int"
    | Type -> "type"
    | Row -> "row"

let to_doc pt = PPrint.string (to_string pt)

let eq pt pt' = match pt with
    | Int -> (match pt' with
        | Int -> true
        | _ -> false)
    | Type -> (match pt' with
        | Type -> true
        | _ -> false)
    | Row -> (match pt' with
        | Row -> true
        | _ -> false)

