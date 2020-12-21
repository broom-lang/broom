open Streaming

open Broom_lib
module TS = TyperSigs
module Env = Typer.Env
module C = Cmdliner
module PP = PPrint

let name = "broom"
let name_c = String.capitalize_ascii name
let prompt = name ^ "> "

let debug_heading str =
    print_endline (str ^ "\n" ^ String.make (String.length str) '=' ^ "\n")
let pwrite output = PP.ToChannel.pretty 1.0 80 output
let pprint = pwrite stdout
let pprint_err = pwrite stderr

let eval_envs () = (Typer.Env.eval (), Fc.Eval.Namespace.create ())

let build debug check_only filename outfile =
    let open PPrint in
    let (let*) = Result.bind in
    let input = open_in filename in
    let output = if not check_only then open_out outfile else stdout in
    let tenv = Typer.Env.program () in
    Fun.protect (fun () ->
        let input = Sedlexing.Utf8.from_channel input in

        match (
            let* defs = Parse.parse_defs input |> Result.map_error parse_err in
            if debug then begin
                print_newline ();
                debug_heading "Parsed AST";
                let doc = PPrint.(group (separate_map (semi ^^ break 1) Ast.Term.Stmt.def_to_doc
                    (Vector.to_list defs))) in
                pprint (doc ^^ twice hardline);
            end;

            let program =
                let pos = match Vector1.of_vector defs with
                    | Some defs ->
                        let ((start, _), _, _) = Vector1.get defs 0 in
                        let ((_, stop), _, _) = Vector1.get defs (Vector1.length defs - 1) in
                        (start, stop)
                    | None ->
                        let pos = {Lexing.pos_fname = filename; pos_lnum = 1; pos_bol = 0; pos_cnum = 0} in
                        (pos, pos) in
                let entry = {Util.pos; v = Ast.Term.Expr.App ( {pos; v = Var (Name.of_string "main")}
                    , Explicit, {pos; v = Tuple Vector.empty} )} in
                let block : Ast.Term.Expr.t Util.with_pos = {pos; v = Record (
                    Stream.concat
                        (Stream.from (Vector.to_source defs)
                        |> Stream.map (fun def -> Ast.Term.Stmt.Def def))
                        (Stream.single (Ast.Term.Stmt.Expr entry))
                    |> Stream.into (Vector.sink ()))} in
                {Util.pos; v = Ast.Term.Expr.App ({pos; v = Var (Name.of_string "let")}, Explicit, block)} in
            let program = Expander.expand Expander.Env.empty program in
            if debug then begin
                debug_heading "Expanded AST";
                pprint (Ast.Term.Expr.to_doc program ^^ twice hardline);
            end;

            let* program = Typer.check_program tenv Vector.empty program |> Result.map_error type_err in
            if debug then begin
                debug_heading "FC from Typechecker";
                pprint (Typer.Env.document tenv Fc.Program.to_doc program ^^ twice hardline)
            end;

            let* program = FwdRefs.convert program |> Result.map_error fwd_ref_errs in
            if debug then begin
                debug_heading "Nonrecursive FC";
                pprint (Typer.Env.document tenv Fc.Program.to_doc program ^^ twice hardline)
            end;

            if not check_only then begin
                let program = Cps.Convert.convert (Fc.Type.Prim Int) program in
                if debug then begin
                    debug_heading "CPS from CPS-conversion";
                    pprint (Cps.Program.to_doc program ^^ twice hardline)
                end;

                let program = ScheduleData.schedule program in
                if debug then begin
                    debug_heading "CFG from Dataflow Scheduling";
                    pprint (Cfg.Program.to_doc program ^^ twice hardline)
                end;

                pwrite output (ToJs.emit program)
            end;
            Ok ()
        ) with
        | Ok () -> ()
        | Error err -> (match err with
            | FwdRefs errors ->
                errors |> CCVector.iter (fun err ->
                    pprint_err (FwdRefs.error_to_doc err));
                flush stderr
            | Type (pos, err) ->
                flush stdout;
                pprint_err PPrint.(hardline ^^ Env.document tenv (Typer.TypeError.to_doc pos) err ^^ hardline);
                flush stderr
            | Parse parse_error ->
                prerr_endline (SedlexMenhir.string_of_ParseError parse_error))
    ) ~finally: (fun () ->
        close_in input;
        if not check_only then close_out output
    )

let ep debug (tenv, venv) (stmt : Ast.Term.Stmt.t) =
    let (let*) = Result.bind in

    let* ({TS.term = program; eff}, tenv) =
        Typer.check_interactive_stmt tenv stmt |> Result.map_error type_err in
    let* program = FwdRefs.convert program |> Result.map_error fwd_ref_errs in
    if debug then pprint PPrint.(Env.document tenv Fc.Program.to_doc program ^^ hardline);
    let doc = PPrint.(colon ^^ blank 1 ^^ Env.document tenv Fc.Type.to_doc program.main.typ
        ^/^ bang ^^ blank 1 ^^ Env.document tenv Fc.Type.to_doc eff
        |> group) in
    pprint doc;

    let (venv, v) = Fc.Eval.run venv program in
    pprint PPrint.(hardline ^^ Fc.Eval.Value.to_doc v);

    Ok (tenv, venv)

let rep debug ((tenv, venv) as envs) input =
    let (let*) = Result.bind in
    match (
        let* stmts = Parse.parse_stmts input |> Result.map_error parse_err in
        if debug then begin
            let doc = PPrint.(group (separate_map (semi ^^ break 1) Ast.Term.Stmt.to_doc
                (Vector.to_list stmts))) in
            pprint doc;
            print_newline ()
        end;

        let* envs = Vector.fold (fun envs stmt ->
            Result.bind envs (fun envs -> ep debug envs stmt)
        ) (Ok envs) stmts in
        print_newline ();
        Ok envs 
    ) with
    | Ok envs -> envs
    | Error err ->
        (match err with
        | Parse err ->
            prerr_endline (SedlexMenhir.string_of_ParseError err);
        | Type (pos, err) ->
            flush stdout;
            pprint_err PPrint.(hardline ^^ Env.document tenv (Typer.TypeError.to_doc pos) err ^^ hardline);
            flush stderr;
        | FwdRefs errors ->
            errors |> CCVector.iter (fun err -> pprint_err (FwdRefs.error_to_doc err));
            flush stderr);
        envs

let repl debug =
    let rec loop envs =
        match LNoise.linenoise prompt with
        | None -> ()
        | Some input ->
            let _ = LNoise.history_add input in
            let envs = rep debug envs (Sedlexing.Utf8.from_string input) in
            loop envs in
    print_endline (name_c ^ " prototype REPL. Press Ctrl+D (on *nix, Ctrl+Z on Windows) to quit.");
    loop (Typer.Env.interactive (), Fc.Eval.Namespace.create ())

let lep debug filename =
    let input = open_in filename in
    Fun.protect (fun () ->
        rep debug (eval_envs ()) (Sedlexing.Utf8.from_channel input)
    ) ~finally: (fun () -> close_in input)

(* # CLI Args & Flags *)

let debug =
    let doc = "run compiler in debug mode" in
    C.Arg.(value & flag & info ["debug"] ~doc)

let infile =
    let docv = "INFILE" in
    let doc = "entry point filename" in
    C.Arg.(value & pos 0 string "" & info [] ~docv ~doc)

let outfile =
    let docv = "OUTFILE" in
    let doc = "output file" in
    C.Arg.(value & opt string "a.js" & info ["o"; "outfile"] ~docv ~doc)

(* # Subcommands *)

let build_t =
    let doc = "compile program" in
    ( C.Term.(const ignore $ (const build $ debug $ const false $ infile $ outfile))
    , C.Term.info "build" ~doc )

let check_t =
    let doc = "typecheck program" in
    ( C.Term.(const ignore $ (const build $ debug $ const true $ infile $ const ""))
    , C.Term.info "check" ~doc )

let eval_t =
    let doc = "evaluate statements" in
    let expr =
        let docv = "STATEMENTS" in
        let doc = "the statements to evaluate" in
        C.Arg.(value & pos 0 string "" & info [] ~docv ~doc) in
    ( C.Term.(const ignore $ (const rep $ debug
        $ (const eval_envs $ const ()) $ (const Sedlexing.Utf8.from_string $ expr)))
    , C.Term.info "eval" ~doc )

let script_t =
    let doc = "evaluate statements from file" in
    let filename =
        let docv = "FILENAME" in
        let doc = "the file to evaluate" in
        C.Arg.(value & pos 0 string "" & info [] ~docv ~doc) in
    ( C.Term.(const ignore $ (const lep $ debug $ filename))
    , C.Term.info "script" ~doc )

let repl_t =
    let doc = "interactive evaluation loop" in
    (C.Term.(const repl $ debug), C.Term.info "repl" ~doc)

let default_t =
    let doc = "effective, modular, functional programming language. WIP." in
    (C.Term.(ret (const (fun () -> `Help (`Pager, None)) $ const ())), C.Term.info name ~doc)

(* # ~ Main *)

let () =
    Hashtbl.randomize ();
    C.Term.exit (C.Term.eval_choice default_t [build_t; check_t; repl_t; script_t; eval_t])

