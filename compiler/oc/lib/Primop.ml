type t =
    | IAdd | ISub | IMul

let of_string = function
    | "iadd" -> Some IAdd
    | "isub" -> Some ISub
    | "imul" -> Some IMul
    | _ -> None

