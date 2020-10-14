module Vector = Vector (* HACK *)
module Vector1 = Vector1

module Util = Util (* HACK *)

module Name = Name

module Ast = Ast
module Fc = struct
    include Fc

    module Eval = FcEval
end

module SedlexMenhir = SedlexMenhir

module Parse = struct
    let parse_defs_exn input =
        SedlexMenhir.create_lexbuf input
        |> SedlexMenhir.sedlex_with_menhir Lexer.token Parser.defs

    let parse_stmts_exn input =
        SedlexMenhir.create_lexbuf input
        |> SedlexMenhir.sedlex_with_menhir Lexer.token Parser.stmts
end

module TyperSigs = TyperSigs (* HACK *)
module Typer = Typer

module ExpandPats = ExpandPats
module FwdRefs = FwdRefs.Make (Hashtbl.Make (struct
    include Int
    let hash = Hashtbl.hash
end))

module Cps = struct
    include Cps

    module Convert = CpsConvert
end

