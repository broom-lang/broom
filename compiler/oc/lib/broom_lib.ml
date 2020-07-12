module Vector = Vector (* HACK *)

module Ast = Ast

module SedlexMenhir = SedlexMenhir

module Parse = struct
    let parse_string_exn input =
        let lexbuf = SedlexMenhir.create_lexbuf (Sedlexing.Utf8.from_string input) in
        SedlexMenhir.sedlex_with_menhir Lexer.token Parser.program lexbuf
end

