type t =
    | Int | Bool
    | Array | String | Cell
    | SingleRep (* = *) | Boxed
    | TypeIn | RowOf

let grammar =
    let open Grammar in let open Grammar.Infix in
    text "int" *> pure Int
    <|> text "bool" *> pure Bool
    <|> text "array" *> pure Array
    <|> text "string" *> pure String
    <|> text "cell" *> pure Cell
    <|> text "singleRep" *> pure SingleRep
    <|> text "boxed" *> pure Boxed
    <|> text "typeIn" *> pure TypeIn
    <|> text "rowOf" *> pure RowOf

let to_doc = PPrinter.of_grammar grammar

let eq = (=)

