type t =
    | Int of int
    | String of string

let to_doc c =
    let open PPrint in
    match c with
    | Int n -> string (Int.to_string n)
    | String s -> dquotes (string s)

