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

type 'a docs_op =
    | InfixL of {prec : int; l : 'a; op : document; r : 'a}
    | InfixR of {prec : int; l : 'a; op : document; r : 'a}
    | Unary of document

let show_paren show doc = if show then PPrint.parens doc else doc

let with_prec to_docs v =
    let rec to_doc ctx_prec v =
        match to_docs ctx_prec v with
        | InfixL {prec; l; op; r} ->
            PPrint.infix 4 1 op (to_doc prec l) (to_doc (prec + 1) r)
            |> show_paren (ctx_prec > prec)

        | InfixR {prec; l; op; r} ->
            PPrint.infix 4 1 op (to_doc (prec + 1) l) (to_doc prec r)
            |> show_paren (ctx_prec > prec)

        | Unary doc -> doc in
    to_doc 0 v

let doc_to_string doc =
    let buf = Buffer.create 0 in
    PPrint.ToBuffer.compact buf doc;
    Buffer.contents buf

