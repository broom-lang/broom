module S = String
module L = SedlexMenhir

let reserved = [%sedlex.regexp? '(' | ')' | '[' | ']' | '{' | '}' | '.' | ':' | ',' | ';' | '|']
let letter = [%sedlex.regexp? ll | lm | lo | lt | lu | pc]
let number = [%sedlex.regexp? nd | nl | no]
let symchar = [%sedlex.regexp? Sub ((pd | pe | pf | pi | po | ps | sc | sk | sm | so), reserved)]

let initial = [%sedlex.regexp? letter]
let constituent = [%sedlex.regexp? initial | symchar | number]

let identifier = [%sedlex.regexp? initial, Star constituent]
let symbol = [%sedlex.regexp? symchar, Star constituent]

let string = [%sedlex.regexp? '"', Star (Compl '"'), '"']
let integer = [%sedlex.regexp? Plus ('0'..'9')]

let rec token ({SedlexMenhir.stream; _} as lexbuf) =
    match%sedlex stream with
    | Plus (Chars " \t\r") -> L.update lexbuf; token lexbuf 
    | '\n' -> L.update lexbuf; L.new_line lexbuf; token lexbuf
    | "--", Star (Compl '\n') -> L.update lexbuf; token lexbuf
    | eof -> L.update lexbuf; Parser.EOF

    | "-!" -> L.update lexbuf; EFFOW
    | "->" -> L.update lexbuf; ARROW
    | "<-" -> L.update lexbuf; LARROW
    | "=>" -> L.update lexbuf; DARROW

    | "||" -> L.update lexbuf; DISJUNCTION (L.lexeme lexbuf)
    | "&&" -> L.update lexbuf; CONJUNCTION (L.lexeme lexbuf)
    | "==" | '<' | '>' | "<=" | ">=" -> L.update lexbuf; COMPARISON (L.lexeme lexbuf)
    | '+' | '-' -> L.update lexbuf; ADDITIVE (L.lexeme lexbuf)
    | '*' | '/' -> L.update lexbuf; MULTIPLICATIVE (L.lexeme lexbuf)

    | '='  -> L.update lexbuf; EQ
    | ':'  -> L.update lexbuf; COLON
    | '.'  -> L.update lexbuf; DOT
    | ','  -> L.update lexbuf; COMMA
    | ';'  -> L.update lexbuf; SEMI
    | '!'  -> L.update lexbuf; BANG
    | '|'  -> L.update lexbuf; BAR
    | '@'  -> L.update lexbuf; AT
    | '?'  -> L.update lexbuf; QMARK
    | '\\' -> L.update lexbuf; BACKSLASH

    | '(' -> L.update lexbuf; LPAREN
    | ')' -> L.update lexbuf; RPAREN
    | '[' -> L.update lexbuf; LBRACKET
    | ']' -> L.update lexbuf; RBRACKET
    | '{' -> L.update lexbuf; LBRACE
    | '}' -> L.update lexbuf; RBRACE

    | string ->
        let tok = L.lexeme lexbuf in
        L.update lexbuf; STRING (S.sub tok 1 (S.length tok - 2))
    | integer -> L.update lexbuf; INT (int_of_string (L.lexeme lexbuf))

    | "__", Plus constituent ->
        let tok = L.lexeme lexbuf in
        L.update lexbuf; PRIMOP (S.sub tok 2 (S.length tok - 2))
    | '_', Star constituent ->
        let tok = L.lexeme lexbuf in
        L.update lexbuf; WILD (S.sub tok 1 (S.length tok - 1))

    | identifier -> L.update lexbuf; ID (L.lexeme lexbuf)
    | symbol -> L.update lexbuf; OP (L.lexeme lexbuf)

    | _ -> L.raise_ParseError lexbuf

