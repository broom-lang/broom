type t =
    | IAdd | ISub | IMul

let of_string = function
    | "iadd" -> Some IAdd
    | "isub" -> Some ISub
    | "imul" -> Some IMul
    | _ -> None

let to_string op =
    let name = match op with
        | IAdd -> "iadd"
        | ISub -> "isub"
        | IMul -> "imul" in
    name

let to_doc op = PPrint.string (to_string op)

