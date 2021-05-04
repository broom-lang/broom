type t =
    | Unit
    | Int of int
    | String of string

let int = PIso.piso (fun n -> Some (Int n)) (function
    | Int n -> Some n
    | _ -> None)

let string = PIso.piso (fun s -> Some (String s)) (function
    | String s -> Some s
    | _ -> None)

let grammar =
    let open Grammar.Infix in
    let strings =
        let open Grammar in
        let cs = many (PIso.subset ((<>) '"') <$> char) in
        let f = PIso.piso
            (fun cs -> Some (List.to_seq cs |> String.of_seq))
            (fun s -> Some (String.to_seq s |> List.of_seq)) in
        token '"' *> (f <$> cs) <* token '"' in
    Grammar.(parens (pure Unit))
    <|> (int <$> Grammar.int)
    <|> (string <$> strings)

let to_doc = PPrinter.of_grammar grammar

