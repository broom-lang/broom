open Broom_lib
module TS = TyperSigs
module Env = Typer.Env
module C = Cmdliner

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

let name = "broom"
let name_c = String.capitalize_ascii name
let prompt = name ^ "> "

let eval_envs () = (Typer.Env.eval (), Fc.Eval.Env.eval ())

let ep ((tenv, venv) as envs) stmt =
    try begin
        let ({TS.term = stmts; TS.eff}, typ, tenv) = Typer.check_stmt tenv stmt in

        match FwdRefs.convert stmts with
        | Ok stmts ->
            stmts |> Vector.iter (fun stmt ->
                let doc = Env.document tenv Fc.Term.Stmt.to_doc stmt ^^ PPrint.semi
                    ^/^ PPrint.colon ^^ PPrint.blank 1 ^^ Env.document tenv Fc.Type.to_doc typ
                    ^/^ PPrint.bang ^^ PPrint.blank 1 ^^ Env.document tenv Fc.Type.to_doc eff
                    |> PPrint.group in
                PPrint.ToChannel.pretty 1.0 80 stdout (PPrint.hardline ^^ doc));

            stmts |> Vector.fold (fun (tenv, venv) stmt ->
                let (v, venv) = Fc.Eval.run venv stmt in
                PPrint.ToChannel.pretty 1.0 80 stdout (PPrint.hardline ^^ Fc.Eval.Value.to_doc v);
                (tenv, venv)
            ) (tenv, venv)
        | Error errors ->
            errors |> CCVector.iter (fun err ->
                PPrint.ToChannel.pretty 1.0 80 stderr (FwdRefs.error_to_doc err));
            flush stderr;
            envs
    end with
    | Typer.TypeError.TypeError (pos, err) ->
        flush stdout;
        PPrint.ToChannel.pretty 1.0 80 stderr
            (PPrint.hardline ^^ Env.document tenv (Typer.TypeError.to_doc pos) err ^^ PPrint.hardline);
        flush stderr;
        envs

let rep envs input =
    try
        let stmts = Parse.parse_commands_exn input in
        let doc = PPrint.group (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) Ast.Term.Stmt.to_doc
            (Vector.to_list stmts)) in
        PPrint.ToChannel.pretty 1.0 80 stdout doc;
        print_newline ();

        let envs = Vector.fold ep envs stmts in
        print_newline ();
        envs
    with
        | SedlexMenhir.ParseError err ->
            prerr_endline (SedlexMenhir.string_of_ParseError err);
            envs

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
    let expr =
        let docv = "FILENAME" in
        let doc = "the file to evaluate" in
        C.Arg.(value & pos 0 string "" & info [] ~docv ~doc) in
    (C.Term.(const ignore $ (const lep $ (const eval_envs $ const ()) $ expr)), C.Term.info "script" ~doc)

let repl_t =
    let doc = "interactive evaluation loop" in
    (C.Term.(const repl $ const ()), C.Term.info "repl" ~doc)

let default_t =
    let doc = "effective, modular, functional programming language. WIP." in
    (C.Term.(ret (const (fun () -> `Help (`Pager, None)) $ const ())), C.Term.info name ~doc)

let () =
    Hashtbl.randomize ();
    C.Term.exit (C.Term.eval_choice default_t [repl_t; script_t; eval_t])

