type plicity = Explicit | Implicit

let plicity_arrow = function
    | Explicit -> PPrint.string "->"
    | Implicit -> PPrint.string "=>"

type span = Lexing.position * Lexing.position

let pos_to_string ({pos_lnum = line; pos_bol = bol; pos_cnum = offset; pos_fname = _} : Lexing.position) =
    Int.to_string line ^ ":" ^ Int.to_string (offset - bol)
let span_to_string (pos, pos') = pos_to_string pos ^ "-" ^ pos_to_string pos'

type 'a with_pos = {v : 'a; pos: span}

let doc_to_string doc =
    let buf = Buffer.create 0 in
    PPrint.ToBuffer.compact buf doc;
    Buffer.contents buf

