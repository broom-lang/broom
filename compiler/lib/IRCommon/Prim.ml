type t =
    | Unit
    | Int | Bool
    | Array | String | Cell
    | SingleRep (* = *) | Boxed | UnitRep | PairRep
    | TypeIn | RowOf

let grammar =
    let open Grammar in let open Grammar.Infix in
    text "unit" *> pure Unit
    <|> text "int" *> pure Int
    <|> text "bool" *> pure Bool
    <|> text "array" *> pure Array
    <|> text "string" *> pure String
    <|> text "cell" *> pure Cell
    <|> text "singleRep" *> pure SingleRep
    <|> text "boxed" *> pure Boxed
    <|> text "unitRep" *> pure UnitRep
    <|> text "pairRep" *> pure PairRep
    <|> text "typeIn" *> pure TypeIn
    <|> text "rowOf" *> pure RowOf

let to_doc = PPrinter.of_grammar grammar

let eq = (=)

