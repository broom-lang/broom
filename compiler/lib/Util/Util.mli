type document = PPrint.document

type plicity = Explicit | Implicit

val plicity_arrow : plicity -> document

type span = Lexing.position * Lexing.position

val span_to_string : span -> string

type 'a with_pos = {v : 'a; pos: span}

type 'a docs_op =
    | InfixL of {prec : int; l : 'a; op : document; r : 'a}
    | InfixR of {prec : int; l : 'a; op : document; r : 'a}
    | Unary of document

val with_prec : (int -> 'a -> 'a docs_op) -> 'a -> document

val doc_to_string : document -> string

