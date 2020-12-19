open Streaming

open Broom_lib
module TS = TyperSigs
module Env = Typer.Env
module C = Cmdliner
module PP = PPrint

let name = "broom"
let name_c = String.capitalize_ascii name
let prompt = name ^ "> "

let pwrite output = PP.ToChannel.pretty 1.0 80 output
let pprint = pwrite stdout
let pprint_err = pwrite stderr

let eval_envs () = (Typer.Env.eval (), Fc.Eval.Env.eval ())

let ep ((tenv, venv) as envs) (stmt : Ast.Term.Stmt.t) =
    try begin
        let (program, eff) : Fc.Program.t * Fc.Type.t = match stmt with
            | Def def ->
                ( Typer.check_program tenv (Vector.singleton def)
                    {v = Tuple Vector.empty; pos = Ast.Term.Stmt.pos stmt}
                , Fc.Type.EmptyRow )
            | Expr expr ->
                let {TS.term; eff} = Typer.typeof tenv expr in
                ( { type_fns = Env.type_fns tenv (* FIXME: gets all typedefs ever seen *)
                  ; defs = Vector.empty; main = term }
                , eff ) in

        match FwdRefs.convert program with
        | Ok program ->
            let doc = PPrint.(Env.document tenv Fc.Program.to_doc program
                ^/^ colon ^^ blank 1 ^^ Env.document tenv Fc.Type.to_doc program.main.typ
                ^/^ bang ^^ blank 1 ^^ Env.document tenv Fc.Type.to_doc eff
                |> group) in
            pprint PPrint.(hardline ^^ doc);

            let (v, venv) = Fc.Eval.run venv program in
            pprint PPrint.(hardline ^^ Fc.Eval.Value.to_doc v);
            (tenv, venv)
        | Error errors ->
            errors |> CCVector.iter (fun err -> pprint_err (FwdRefs.error_to_doc err));
            flush stderr;
            envs
    end with
    | Typer.TypeError.TypeError (pos, err) ->
        flush stdout;
        pprint_err PPrint.(hardline ^^ Env.document tenv (Typer.TypeError.to_doc pos) err ^^ hardline);
        flush stderr;
        envs

let rep envs input =
    try
        let stmts = Parse.parse_stmts_exn input in
        let doc = PPrint.(group (separate_map (semi ^^ break 1) Ast.Term.Stmt.to_doc
            (Vector.to_list stmts))) in
        pprint doc;
        print_newline ();

        let envs = Vector.fold ep envs stmts in
        print_newline ();
        envs
    with
        | SedlexMenhir.ParseError err ->
            prerr_endline (SedlexMenhir.string_of_ParseError err);
            envs

let build debug check_only filename outfile =
    let open PPrint in
    let input = open_in filename in
    let output = if not check_only then open_out outfile else stdout in
    let tenv = Typer.Env.program () in
    Fun.protect (fun () ->
        let input = Sedlexing.Utf8.from_channel input in
        try
            let defs = Parse.parse_defs_exn input in
            if debug then begin
                print_endline "\nParsed AST\n==========\n";
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
                print_endline "Expanded AST\n============\n";
                pprint (Ast.Term.Expr.to_doc program ^^ twice hardline);
            end;

            let program = Typer.check_program tenv Vector.empty program in
            if debug then begin
                print_endline "FC from Typechecker\n===================\n";
                pprint (Typer.Env.document tenv Fc.Program.to_doc program ^^ twice hardline)
            end;

            match FwdRefs.convert program with
            | Ok program ->
                if debug then begin
                    print_endline "Nonrecursive FC\n===============\n";
                    pprint (Typer.Env.document tenv Fc.Program.to_doc program ^^ twice hardline)
                end;

                if not check_only then begin
                    let program = Cps.Convert.convert (Fc.Type.Prim Int) program in
                    if debug then begin
                        print_endline "CPS from CPS-conversion\n=======================\n";
                        pprint (Cps.Program.to_doc program ^^ twice hardline)
                    end;

                    let program = ScheduleData.schedule program in
                    if debug then begin
                        print_endline "CFG from Dataflow Scheduling\n============================\n";
                        pprint (Cfg.Program.to_doc program ^^ twice hardline)
                    end;

                    let js = ToJs.emit program in
                    pwrite output js
                end
            | Error errors ->
                errors |> CCVector.iter (fun err ->
                    pprint_err (FwdRefs.error_to_doc err));
                flush stderr
        with
        | SedlexMenhir.ParseError err ->
            prerr_endline (SedlexMenhir.string_of_ParseError err);
        | Typer.TypeError.TypeError (pos, err) ->
            flush stdout;
            pprint_err PPrint.(hardline ^^ Env.document tenv (Typer.TypeError.to_doc pos) err ^^ hardline);
            flush stderr;
    ) ~finally: (fun () ->
        close_in input;
        if not check_only then close_out output
    )

let lep envs filename =
    let input = open_in filename in
    Fun.protect (fun () ->
        rep envs (Sedlexing.Utf8.from_channel input)
    ) ~finally: (fun () -> close_in input)

let repl () =
    let rec loop envs =
        match LNoise.linenoise prompt with
        | None -> ()
        | Some input ->
            let _ = LNoise.history_add input in
            let envs = rep envs (Sedlexing.Utf8.from_string input) in
            loop envs in
    print_endline (name_c ^ " prototype REPL. Press Ctrl+D (on *nix, Ctrl+Z on Windows) to quit.");
    loop (Typer.Env.interactive (), Fc.Eval.Env.interactive ())

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
    ( C.Term.(const ignore $ (const rep $ (const eval_envs $ const ()) $ (const Sedlexing.Utf8.from_string $ expr)))
    , C.Term.info "eval" ~doc )

let script_t =
    let doc = "evaluate statements from file" in
    let filename =
        let docv = "FILENAME" in
        let doc = "the file to evaluate" in
        C.Arg.(value & pos 0 string "" & info [] ~docv ~doc) in
    ( C.Term.(const ignore $ (const lep $ (const eval_envs $ const ()) $ filename))
    , C.Term.info "script" ~doc )

let repl_t =
    let doc = "interactive evaluation loop" in
    (C.Term.(const repl $ const ()), C.Term.info "repl" ~doc)

let default_t =
    let doc = "effective, modular, functional programming language. WIP." in
    (C.Term.(ret (const (fun () -> `Help (`Pager, None)) $ const ())), C.Term.info name ~doc)

let () =
    Hashtbl.randomize ();
    C.Term.exit (C.Term.eval_choice default_t [build_t; check_t; repl_t; script_t; eval_t])

