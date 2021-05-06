open Streaming

type document = PPrint.document

type plicity = Explicit | Implicit

let plicity_arrow = function
    | Explicit -> PPrint.string "->"
    | Implicit -> PPrint.string "=>"

type span = Lexing.position * Lexing.position

let pos_to_string ({pos_lnum = line; pos_bol = bol; pos_cnum = offset; pos_fname = _} : Lexing.position) =
    Int.to_string line ^ ":" ^ Int.to_string (offset - bol)
let span_to_string (pos, pos') = pos_to_string pos ^ "-" ^ pos_to_string pos'

type 'a with_pos = {v : 'a; pos: span}

let ccvector_to_source vec = Source.seq (CCVector.to_seq vec)

type 'a docs_op =
    | InfixL of {prec : int; l : 'a; op : document; r : 'a}
    | InfixR of {prec : int; l : 'a; op : document; r : 'a}
    | Prefix of {prec : int; op : document; arg : 'a}
    | Postfix of {prec : int; arg : 'a; op : document}
    | Unary of document

let show_paren show doc = if show then PPrint.parens doc else doc

let with_prec to_docs ctx_prec v =
    let open PPrint in

    let rec to_doc ctx_prec v =
        match to_docs v with
        | InfixL {prec; l; op; r} ->
            infix 4 1 op (to_doc prec l) (to_doc (prec + 1) r)
            |> show_paren (ctx_prec > prec)

        | InfixR {prec; l; op; r} ->
            infix 4 1 op (to_doc (prec + 1) l) (to_doc prec r)
            |> show_paren (ctx_prec > prec)

        | Prefix {prec; op; arg} ->
            prefix 4 1 op (to_doc prec arg)
            |> show_paren (ctx_prec > prec)

        | Postfix {prec; op; arg} ->
            prefix 4 1 (to_doc prec arg) op
            |> show_paren (ctx_prec > prec)

        | Unary doc -> doc in
    to_doc ctx_prec v

let doc_to_string doc =
    let buf = Buffer.create 0 in
    PPrint.ToBuffer.compact buf doc;
    Buffer.contents buf

let debug_heading str =
    print_endline ("\n" ^ str ^ "\n" ^ String.make (String.length str) '=' ^ "\n")
let pwrite output = PPrint.ToChannel.pretty 1.0 80 output
let pprint = pwrite stdout
let pprint_err = pwrite stderr

