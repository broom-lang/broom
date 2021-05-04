type t =
    | Pair | Fst | Snd
    | CellNew | CellInit | CellGet
    | Int | String | Type
    | TypeOf (* TODO: get rid of this? *)
    | Import
    | GlobalSet | GlobalGet

let of_string = function
    | "pair" -> Some Pair
    | "fst" -> Some Fst
    | "snd" -> Some Snd
    | "cellNew" -> Some CellNew
    | "cellInit" -> Some CellInit
    | "cellGet" -> Some CellGet
    | "int" -> Some Int
    | "string" -> Some String
    | "type" -> Some Type
    | "typeOf" -> Some TypeOf
    | "import" -> Some Import
    | "globalSet" -> Some GlobalSet
    | "globalGet" -> Some GlobalGet
    | _ -> None

let to_string = function
    | Pair -> "pair"
    | Fst -> "fst"
    | Snd -> "snd"
    | CellNew -> "cellNew"
    | CellInit -> "cellInit"
    | CellGet -> "cellGet"
    | Int -> "int"
    | String -> "string"
    | Type -> "type"
    | TypeOf -> "typeOf"
    | Import -> "import"
    | GlobalSet -> "globalSet"
    | GlobalGet -> "globalGet"

let grammar =
    let open Grammar in let open Grammar.Infix in
    text "pair" *> pure Pair
    <|> text "fst" *> pure Fst
    <|> text "snd" *> pure Snd
    <|> text "cellNew" *> pure CellNew
    <|> text "cellInit" *> pure CellInit
    <|> text "cellGet" *> pure CellGet
    <|> text "int" *> pure Int
    <|> text "string" *> pure String
    <|> text "type" *> pure Type
    <|> text "typeOf" *> pure TypeOf
    <|> text "import" *> pure Import
    <|> text "globalSet" *> pure GlobalSet
    <|> text "globalGet" *> pure GlobalGet

let to_doc = PPrinter.of_grammar grammar

let is_pure = function
    | Pair | Fst | Snd
    | CellNew | Int | String | Type | TypeOf -> true
    | CellInit | CellGet | Import (* ? *) | GlobalSet | GlobalGet -> false

