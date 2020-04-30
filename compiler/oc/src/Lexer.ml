open SedlexMenhir

open Parser

let initial = [%sedlex.regexp? '_' | alphabetic]
let constituent = [%sedlex.regexp? initial | '0'..'9']
let identifier = [%sedlex.regexp? initial, Star constituent]

let integer = [%sedlex.regexp? Plus ('0'..'9')]

let rec token ({stream; _} as lexbuf) =
    match%sedlex stream with
    | "fun"  -> update lexbuf; FUN
    | "pi"   -> update lexbuf; PI
    | "if"   -> update lexbuf; IF
    | "then" -> update lexbuf; THEN
    | "else" -> update lexbuf; ELSE
    | "val"  -> update lexbuf; VAL
    | "type" -> update lexbuf; TYPE

    | "->" -> update lexbuf; ARROW
    | "=>" -> update lexbuf; DARROW
    | '.'  -> update lexbuf; DOT
    | ':'  -> update lexbuf; COLON
    | '='  -> update lexbuf; EQ
    | ';'  -> update lexbuf; SEMI
    | '|'  -> update lexbuf; BAR

    | '(' -> update lexbuf; LPAREN
    | ')' -> update lexbuf; RPAREN
    | '[' -> update lexbuf; LBRACKET
    | ']' -> update lexbuf; RBRACKET
    | '{' -> update lexbuf; LBRACE
    | '}' -> update lexbuf; RBRACE

    | identifier -> update lexbuf; ID (lexeme lexbuf)
    | integer -> update lexbuf; CONST (int_of_string (lexeme lexbuf))

    | Plus (Chars " \t\r") -> update lexbuf; token lexbuf 
    | '\n' -> update lexbuf; new_line lexbuf; token lexbuf
    | eof -> update lexbuf; EOF

    | _ -> raise_ParseError lexbuf

