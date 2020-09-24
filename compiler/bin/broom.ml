open Broom_lib
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
        let ({term = stmt; typ; eff}, tenv) : Fc.Term.Stmt.t Typer.typing * _ = Typer.check_stmt tenv stmt in
        let doc = Env.document tenv Fc.Term.Stmt.to_doc stmt ^^ PPrint.semi
            ^/^ PPrint.colon ^^ PPrint.blank 1 ^^ Env.document tenv Fc.Type.to_doc typ
            ^/^ PPrint.bang ^^ PPrint.blank 1 ^^ Env.document tenv Fc.Type.to_doc eff
            |> PPrint.group in
        PPrint.ToChannel.pretty 1.0 80 stdout (PPrint.hardline ^^ doc);

        let res = Fc.Eval.run venv stmt in
        let (chan, vdoc) = match res with
            | Ok v -> (stdout, Fc.Eval.Value.to_doc v)
            | Error err -> (stderr, PPrint.string "Runtime error:" ^/^ Fc.Eval.Error.to_doc err) in
        PPrint.ToChannel.pretty 1.0 80 chan (PPrint.hardline ^^ vdoc);
        (tenv, venv)
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

let repl () =
    let rec loop envs =
        match LNoise.linenoise prompt with
        | None -> ()
        | Some input ->
            let _ = LNoise.history_add input in
            let envs = rep envs input in
            loop envs in
    print_endline (name_c ^ " prototype REPL. Press Ctrl+D (on *nix, Ctrl+Z on Windows) to quit.");
    loop (Typer.Env.interactive (), Fc.Eval.Env.interactive ())

(* FIXME: Global scope is not created, leading to unbound variables galore: *)
let eval_t =
    let doc = "evaluate statements" in
    let expr =
        let docv = "STATEMENTS" in
        let doc = "the statements to evaluate" in
        C.Arg.(value & pos 0 string "" & info [] ~docv ~doc) in
    (C.Term.(const ignore $ (const rep $ (const eval_envs $ const ()) $ expr)), C.Term.info "eval" ~doc)

let repl_t =
    let doc = "interactive evaluation loop" in
    (C.Term.(const repl $ const ()), C.Term.info "repl" ~doc)

let default_t =
    let doc = "effective, modular, functional programming language. WIP." in
    (C.Term.(ret (const (fun () -> `Help (`Pager, None)) $ const ())), C.Term.info name ~doc)

let () =
    Hashtbl.randomize ();
    C.Term.exit (C.Term.eval_choice default_t [repl_t; eval_t])

