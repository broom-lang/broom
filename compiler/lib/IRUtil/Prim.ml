type t =
    | Int | Bool
    | Array | Cell
    | SingleRep (* = *) | Boxed
    | TypeIn | RowOf

let to_string = function
    | Int -> "int"
    | Bool -> "bool"
    | Array -> "array"
    | Cell -> "cell"
    | SingleRep -> "singleRep"
    | Boxed -> "boxed"
    | TypeIn -> "typeIn"
    | RowOf -> "rowOf"

let to_doc pt = PPrint.string (to_string pt)

let eq = (=)

