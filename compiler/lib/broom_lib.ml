module Vector = Vector (* HACK *)
module Util = Util (* HACK *)

module Ast = Ast
module Fc = struct
    include Fc

    module Eval = FcEval
end

module SedlexMenhir = SedlexMenhir

module Parse = struct
    let program filename input =
        try
            SedlexMenhir.create_lexbuf filename input
            |> SedlexMenhir.sedlex_with_menhir Lexer.token Parser.program
            |> fun program -> Ok program
        with SedlexMenhir.ParseError err -> Error err

    let parse_stmts filename input =
        try
            SedlexMenhir.create_lexbuf filename input
            |> SedlexMenhir.sedlex_with_menhir Lexer.token Parser.stmts
            |> fun stmts -> Ok stmts
        with SedlexMenhir.ParseError err -> Error err
end

module Expander = Expander.Make (Hashtbl.Make (struct
    type t = string

    let equal = String.equal
    let hash = Hashtbl.hash
end))

module TyperSigs = TyperSigs (* HACK *)
module Typer = Typer

(*module ExpandPats = ExpandPats*)
module FwdRefs = FwdRefs

type error =
    | Parse of SedlexMenhir.parse_error
    | Type of Typer.Error.t list
    | FwdRefs of FwdRefs.error CCVector.ro_vector

let parse_err err = Parse err
let type_err errs = Type errs
let fwd_ref_errs errs = FwdRefs errs

module Value = Value
module Namespace = Namespace

module Compiler = struct
    open PPrint

    let check_program ~debug ~path program =
        let (let*) = Result.bind in
        let (let+) = Fun.flip Result.map in

        let program = Expander.expand_program (Expander.Bindings.empty path) program in
        if debug then begin
            Util.debug_heading "Expanded AST";
            Util.pprint (Ast.Program.to_doc program ^^ hardline);
        end;

        let* {term = program; eff = _} =
            Typer.check_program program |> Result.map_error type_err in
        if debug then begin
            Util.debug_heading "FC from Typechecker";
            Util.pprint (Fc.Program.to_doc program ^^ hardline)
        end;

        let+ program = FwdRefs.convert program |> Result.map_error fwd_ref_errs in
        if debug then begin
            Util.debug_heading "Nonrecursive FC";
            Util.pprint (Fc.Program.to_doc program ^^ hardline)
        end;

        program

    let check_interactive_stmt ~debug eenv ns (stmt : Ast.Term.Stmt.t) =
        let (let*) = Result.bind in
        let (let+) = Fun.flip Result.map in

        let (eenv, stmts) = Expander.expand_interactive_stmt eenv stmt in
        if debug then begin
            Util.debug_heading "Expanded AST";
            let doc = separate_map (semi ^^ break 1) Ast.Term.Stmt.to_doc (Vector1.to_list stmts) in
            Util.pprint (doc ^^ hardline);
        end;

        let* ({TyperSigs.term = program; eff}, ns) =
            Typer.check_interactive_stmts ns stmts |> Result.map_error type_err in
        if debug then begin
            Util.debug_heading "FC from Typechecker";
            Util.pprint (Fc.Program.to_doc program ^^ hardline)
        end;

        let+ program = FwdRefs.convert program |> Result.map_error fwd_ref_errs in
        if debug then begin
            Util.debug_heading "Nonrecursive FC";
            Util.pprint (Fc.Program.to_doc program ^^ hardline)
        end;

        (eenv, ns, {TyperSigs.term = program; eff})

    let compile_program ~debug ~path ~output defs =
        let (let+) = Fun.flip Result.map in

        let+ program = check_program ~debug ~path defs in
        let program = MiddleEnd.to_cfg ~debug program in
        Util.pwrite output (ToJs.emit program)
end

