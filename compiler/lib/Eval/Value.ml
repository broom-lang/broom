type t =
    | Tuple of t Vector.t
    | Fn of ((t -> t) -> t -> t)
    | Record of t Name.Map.t
    | Proxy
    | Cell of t option ref
    | Int of int
    | Bool of bool
    | String of string

let rec to_doc =
    let open PPrint in
    function
    | Tuple vs -> surround_separate_map 4 0 (parens empty)
        lparen (comma ^^ break 1) rparen
        to_doc (Vector.to_list vs)
    | Fn _ -> braces (bar ^^ blank 1 ^^ infix 4 1 (string "->") underscore underscore)
    | Record fields ->
        let field_to_doc (label, v) =
            infix 4 1 equals (Name.to_doc label) (to_doc v) in
        surround_separate_map 4 0 (braces empty)
            lbrace (comma ^^ break 1) rbrace
            field_to_doc (Name.Map.bindings fields)
    | Proxy -> brackets underscore
    | Cell v -> sharp ^^ angles (string "cell" ^/^ match !v with
        | Some contents -> to_doc contents
        | None -> string "uninitialized")
    | Int n -> string (Int.to_string n)
    | Bool true -> string "True"
    | Bool false -> string "False"
    | String s -> dquotes (string s)

