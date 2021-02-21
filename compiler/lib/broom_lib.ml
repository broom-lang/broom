module Asserts = Asserts

module StringHashtbl = Hashtbl.Make (struct
    type t = string

    let equal = String.equal
    let hash = Hashtbl.hash
end)
module Vector = Vector (* HACK *)
module Vector1 = Vector1

module Util = Util (* HACK *)

module Name = Name

module Ast = Ast

module Fc = struct
    include ComplexFc

    module Eval = ComplexFcEval
end

module SedlexMenhir = SedlexMenhir

module Parse = struct
    let parse_defs filename input =
        try
            SedlexMenhir.create_lexbuf filename input
            |> SedlexMenhir.sedlex_with_menhir Lexer.token Parser.defs
            |> fun defs -> Ok defs
        with SedlexMenhir.ParseError err -> Error err

    let parse_stmts filename input =
        try
            SedlexMenhir.create_lexbuf filename input
            |> SedlexMenhir.sedlex_with_menhir Lexer.token Parser.stmts
            |> fun stmts -> Ok stmts
        with SedlexMenhir.ParseError err -> Error err
end

module Expander = Expander.Make (StringHashtbl)

module TyperSigs = TyperSigs (* HACK *)
module Typer = struct
    include Typer

    module Finish = FinishTyping
end

module ExpandPats = ExpandPats
(*module FwdRefs = FwdRefs*)

type error =
    | Parse of SedlexMenhir.parse_error
    | Type of (Util.span * Typer.TypeError.t) list
    (*| FwdRefs of FwdRefs.error CCVector.ro_vector*)

let parse_err err = Parse err
let type_err err = Type err
(*let fwd_ref_errs errs = FwdRefs errs*)

(*
module Cps = struct
    include Cps

    module Convert = CpsConvert
end

module Untuple = Untuple

module Cfg = Cfg
module ScheduleData = ScheduleData

module ToJs = ToJs
*)

