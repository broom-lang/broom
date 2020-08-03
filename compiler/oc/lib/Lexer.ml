open SedlexMenhir

open Parser

let initial = [%sedlex.regexp? alphabetic]
let constituent = [%sedlex.regexp? initial | '0'..'9']
let identifier = [%sedlex.regexp? initial, Star constituent]

let integer = [%sedlex.regexp? Plus ('0'..'9')]

let rec token ({stream; _} as lexbuf) =
    match%sedlex stream with
    | "->" -> update lexbuf; ARROW
    | "=>" -> update lexbuf; DARROW
    | "<-" -> update lexbuf; LARROW

    (* FIXME: actually design infix operators: *)
    | "||" -> update lexbuf; OP1 (lexeme lexbuf)
    | "&&" -> update lexbuf; OP2 (lexeme lexbuf)
    | "==" | '<' | '>' | "<=" | ">=" -> update lexbuf; OP3 (lexeme lexbuf)
    | '+' | '-' -> update lexbuf; OP4 (lexeme lexbuf)
    | '*' | '/' | '%' -> update lexbuf; OP5 (lexeme lexbuf)

    | '='  -> update lexbuf; EQ
    | ':'  -> update lexbuf; COLON
    | '.'  -> update lexbuf; DOT
    | ','  -> update lexbuf; COMMA
    | ';'  -> update lexbuf; SEMI
    | '!'  -> update lexbuf; BANG
    | '|'  -> update lexbuf; BAR
    | '@'  -> update lexbuf; AT

    | '(' -> update lexbuf; LPAREN
    | ')' -> update lexbuf; RPAREN
    | '[' -> update lexbuf; LBRACKET
    | ']' -> update lexbuf; RBRACKET
    | '{' -> update lexbuf; LBRACE
    | '}' -> update lexbuf; RBRACE

    | "__", Plus constituent ->
        let tok = lexeme lexbuf in
        update lexbuf; PRIMOP (String.sub tok 2 (String.length tok - 2))
    | '_', Star constituent ->
        let tok = lexeme lexbuf in
        update lexbuf; WILD (String.sub tok 1 (String.length tok - 1))

    | identifier -> update lexbuf; ID (lexeme lexbuf)
    | integer -> update lexbuf; CONST (int_of_string (lexeme lexbuf))

    | Plus (Chars " \t\r") -> update lexbuf; token lexbuf 
    | '\n' -> update lexbuf; new_line lexbuf; token lexbuf
    | eof -> update lexbuf; EOF

    | _ -> raise_ParseError lexbuf

