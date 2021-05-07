open Streaming

type document = PPrint.document

type plicity = Explicit | Implicit

val is_implicit : plicity -> bool
val plicity_arrow : plicity -> document

type span = Lexing.position * Lexing.position

val span_to_string : span -> string

type 'a with_pos = {v : 'a; pos: span}

val ccvector_to_source : ('a, 'mut) CCVector.t -> 'a Source.t

type 'a docs_op =
    | InfixL of {prec : int; l : 'a; op : document; r : 'a}
    | InfixR of {prec : int; l : 'a; op : document; r : 'a}
    | Prefix of {prec : int; op : document; arg : 'a}
    | Postfix of {prec : int; arg : 'a; op : document}
    | Unary of document

val with_prec : ('a -> 'a docs_op) -> int -> 'a -> document

val doc_to_string : document -> string
val pwrite : out_channel -> document -> unit
val pprint : document -> unit
val pprint_err : document -> unit

val debug_heading : string -> unit

