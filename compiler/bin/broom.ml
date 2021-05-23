open Broom_lib
module C = Cmdliner

let (let*) = Result.bind
let (let+) = Fun.flip Result.map

let name = "broom"
let name_c = String.capitalize_ascii name
let prompt = name ^ "> "

let eval_envs path = (Expander.Bindings.empty path, Namespace.empty)

let build path debug check_only target filename outfile =
    let open PPrint in

    let input = open_in filename in
    let output = if not check_only then open_out outfile else stdout in
    Fun.protect (fun () ->
        let input = Sedlexing.Utf8.from_channel input in

        match (
            let* program = Parse.program filename input |> Result.map_error parse_err in
            if debug then begin
                print_newline ();
                Util.debug_heading "Parsed AST";
                let doc = Ast.Program.to_doc program in
                Util.pprint (doc ^^ twice hardline);
            end;

            if check_only
            then Result.map ignore (Compiler.check_program ~debug ~path program)
            else Compiler.compile_program target ~debug ~path ~output program
        ) with
        | Ok () -> ()
        | Error err ->
            (match err with
            | Parse err ->
                prerr_endline (SedlexMenhir.string_of_ParseError err);
            | Type errs ->
                flush stdout;
                Util.pprint_err (hardline
                    ^^ separate_map (twice hardline) Typer.Error.to_doc errs
                    ^^ hardline);
                flush stderr;
            | FwdRefs errors ->
                errors |> CCVector.iter (fun err -> Util.pprint_err (FwdRefs.error_to_doc err));
                flush stderr)
    ) ~finally: (fun () ->
        close_in input;
        if not check_only then close_out output
    )

let rep debug envs filename input =
    let open PPrint in

    match (
        let* stmts = Parse.parse_stmts filename input |> Result.map_error parse_err in
        if debug then begin
            Util.debug_heading "\nParsed AST";
            let doc = group (separate_map (semi ^^ break 1) Ast.Stmt.to_doc
                (Vector.to_list stmts)) in
            Util.pprint (doc ^^ twice hardline)
        end;

        let* envs = Vector.fold (fun envs stmt ->
            let* (eenv, ns) = envs in
            let+ (eenv, ns, {TyperSigs.term = program; eff}) =
                Compiler.check_interactive_stmt ~debug eenv ns stmt in

            let v = Fc.Eval.run ns program in
            let doc = infix 4 1 bang
                (infix 4 1 colon (Value.to_doc v)
                    (Fc.Type.to_doc program.main.typ))
                (Fc.Type.to_doc eff) in
            Util.pprint (doc ^^ hardline);

            (eenv, ns)
        ) (Ok envs) stmts in
        print_newline ();
        Ok envs 
    ) with
    | Ok envs -> envs
    | Error err ->
        (match err with
        | Parse err ->
            prerr_endline (SedlexMenhir.string_of_ParseError err);
        | Type errs ->
            flush stdout;
            Util.pprint_err PPrint.(hardline
                ^^ separate_map (twice hardline) Typer.Error.to_doc errs
                ^^ hardline);
            flush stderr;
        | FwdRefs errors ->
            errors |> CCVector.iter (fun err -> Util.pprint_err (FwdRefs.error_to_doc err));
            flush stderr);
        envs

let repl path debug =
    let rec loop envs =
        match LNoise.linenoise prompt with
        | None -> ()
        | Some input ->
            let _ = LNoise.history_add input in
            let envs = rep debug envs "REPL input" (Sedlexing.Utf8.from_string input) in
            loop envs in
    print_endline (name_c ^ " prototype REPL. Press Ctrl+D (on *nix, Ctrl+Z on Windows) to quit.");
    loop (Expander.Bindings.empty path, Namespace.empty)

let lep path debug filename =
    let input = open_in filename in
    Fun.protect (fun () ->
        rep debug (eval_envs path) filename (Sedlexing.Utf8.from_channel input)
    ) ~finally: (fun () -> close_in input)

(* # CLI Args & Flags *)

let path =
    let docv = "BROOMPATH" in
    let env = C.Arg.env_var docv in
    let doc = "Where to look for Broom code; colon-separated, like shell PATH." in
    C.Arg.(value & opt (list ~sep: ':' string) [Filename.current_dir_name]
        & info ["p"; "path"] ~env ~docv ~doc)

let debug =
    let doc = "run compiler in debug mode" in
    C.Arg.(value & flag & info ["debug"] ~doc)

let infile =
    let docv = "INFILE" in
    let doc = "entry point filename" in
    C.Arg.(value & pos 0 string "" & info [] ~docv ~doc)

let target =
    let platforms = [("node", Platform.Node)] in
    let docv = "PLATFORM" in
    let doc = "target platform" in
    C.Arg.(value & opt (enum platforms) Node & info ["t"; "target"] ~docv ~doc)

let outfile =
    let docv = "OUTFILE" in
    let doc = "output file" in
    C.Arg.(value & opt string "a.js" & info ["o"; "outfile"] ~docv ~doc)

(* # Subcommands *)

let build_t =
    let doc = "compile program" in
    ( C.Term.(const ignore $ (const build $ path $ debug $ const false $ target $ infile $ outfile))
    , C.Term.info "build" ~doc )

let check_t =
    let doc = "typecheck program" in
    ( C.Term.(const ignore $ (const build $ path $ debug $ const true $ target $ infile $ const ""))
    , C.Term.info "check" ~doc )

let eval_t =
    let doc = "evaluate statements" in
    let expr =
        let docv = "STATEMENTS" in
        let doc = "the statements to evaluate" in
        C.Arg.(value & pos 0 string "" & info [] ~docv ~doc) in
    ( C.Term.(const ignore $ (const rep $ debug
        $ (const eval_envs $ path) $ const "CLI arg" $ (const Sedlexing.Utf8.from_string $ expr)))
    , C.Term.info "eval" ~doc )

let script_t =
    let doc = "evaluate statements from file" in
    let filename =
        let docv = "FILENAME" in
        let doc = "the file to evaluate" in
        C.Arg.(value & pos 0 string "" & info [] ~docv ~doc) in
    ( C.Term.(const ignore $ (const lep $ path $ debug $ filename))
    , C.Term.info "script" ~doc )

let repl_t =
    let doc = "interactive evaluation loop" in
    (C.Term.(const repl $ path $ debug), C.Term.info "repl" ~doc)

let default_t =
    let doc = "effective, modular, functional programming language. WIP." in
    (C.Term.(ret (const (fun () -> `Help (`Pager, None)) $ const ())), C.Term.info name ~doc)

(* # ~ Main *)

let () =
    Hashtbl.randomize ();
    C.Term.exit (C.Term.eval_choice default_t [build_t; check_t; repl_t; script_t; eval_t])

