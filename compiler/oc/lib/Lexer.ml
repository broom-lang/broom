open SedlexMenhir

open Parser

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

let rec token ({stream; _} as lexbuf) =
    match%sedlex stream with
    | Plus (Chars " \t\r") -> update lexbuf; token lexbuf 
    | '\n' -> update lexbuf; new_line lexbuf; token lexbuf
    | "--", Star (Compl '\n') -> update lexbuf; token lexbuf
    | eof -> update lexbuf; EOF

    | "->" -> update lexbuf; ARROW
    | "<-" -> update lexbuf; LARROW
    | "=>" -> update lexbuf; DARROW

    | "||" -> update lexbuf; DISJUNCTION (lexeme lexbuf)
    | "&&" -> update lexbuf; CONJUNCTION (lexeme lexbuf)
    | "==" | '<' | '>' | "<=" | ">=" -> update lexbuf; COMPARISON (lexeme lexbuf)
    | '+' | '-' -> update lexbuf; ADDITIVE (lexeme lexbuf)
    | '*' | '/' | '%' -> update lexbuf; MULTIPLICATIVE (lexeme lexbuf)

    | '='  -> update lexbuf; EQ
    | ':'  -> update lexbuf; COLON
    | '.'  -> update lexbuf; DOT
    | ','  -> update lexbuf; COMMA
    | ';'  -> update lexbuf; SEMI
    | '!'  -> update lexbuf; BANG
    | '|'  -> update lexbuf; BAR
    | '@'  -> update lexbuf; AT
    | '?'  -> update lexbuf; QMARK
    | '\\' -> update lexbuf; BACKSLASH

    | '(' -> update lexbuf; LPAREN
    | ')' -> update lexbuf; RPAREN
    | '[' -> update lexbuf; LBRACKET
    | ']' -> update lexbuf; RBRACKET
    | '{' -> update lexbuf; LBRACE
    | '}' -> update lexbuf; RBRACE

    | string ->
        let tok = lexeme lexbuf in
        update lexbuf; STRING (String.sub tok 1 (String.length tok - 2))
    | integer -> update lexbuf; INT (int_of_string (lexeme lexbuf))

    | "__", Plus constituent ->
        let tok = lexeme lexbuf in
        update lexbuf; PRIMOP (String.sub tok 2 (String.length tok - 2))
    | '_', Star constituent ->
        let tok = lexeme lexbuf in
        update lexbuf; WILD (String.sub tok 1 (String.length tok - 1))

    | identifier -> update lexbuf; ID (lexeme lexbuf)
    | symbol -> update lexbuf; OP (lexeme lexbuf)

    | _ -> raise_ParseError lexbuf

