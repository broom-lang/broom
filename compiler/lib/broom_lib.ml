module Vector = Vector (* HACK *)

module Util = Util (* HACK *)

module Ast = Ast
module Fc = struct
    include Fc

    module Eval = FcEval
end

module SedlexMenhir = SedlexMenhir

module Parse = struct
    let parse_commands_exn input =
        SedlexMenhir.create_lexbuf input
        |> SedlexMenhir.sedlex_with_menhir Lexer.token Parser.commands
end

module TyperSigs = TyperSigs (* HACK *)
module Typer = Typer

module ExpandPats = ExpandPats
module FwdRefs = FwdRefs.Make (Hashtbl.Make (struct
    include Int
    let hash = Hashtbl.hash
end))

