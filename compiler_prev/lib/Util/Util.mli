type plicity = Explicit | Implicit

val plicity_arrow : plicity -> PPrint.document

type span = Lexing.position * Lexing.position

val span_to_string : span -> string

type 'a with_pos = {v : 'a; pos: span}

val doc_to_string : PPrint.document -> string

