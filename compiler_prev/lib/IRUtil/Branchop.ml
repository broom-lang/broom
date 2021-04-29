type t =
    | IAdd | ISub | IMul | IDiv
    | ILt | ILe | IGt | IGe | IEq

let of_string = function
    | "iadd" -> Some IAdd
    | "isub" -> Some ISub
    | "imul" -> Some IMul
    | "idiv" -> Some IDiv
    | "ilt" -> Some ILt
    | "ile" -> Some ILe
    | "igt" -> Some IGt
    | "ige" -> Some IGe
    | "ieq" -> Some IEq
    | _ -> None

let grammar =
    let open Grammar in let open Grammar.Infix in
    text "iadd" *> pure IAdd
    <|> text "isub" *> pure ISub
    <|> text "imul" *> pure IMul
    <|> text "idiv" *> pure IDiv
    <|> text "ilt" *> pure ILt
    <|> text "ile" *> pure ILe
    <|> text "igt" *> pure IGt
    <|> text "ige" *> pure IGe
    <|> text "ieq" *> pure IEq

let to_doc = PPrinter.of_grammar grammar

