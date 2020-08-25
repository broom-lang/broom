open Broom_lib
module C = Cmdliner

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

let name = "broom"
let name_c = String.capitalize_ascii name
let prompt = name ^ "> "

let ep tenv stmt =
    (try begin
        let ({term; typ; eff}, tenv) : Fc.Term.Stmt.t Typer.typing * _ = Typer.check_stmt tenv stmt in
        let s = Typer.Env.current_uv_subst tenv in
        let doc = Fc.Term.Stmt.to_doc s term ^^ PPrint.semi
            ^/^ PPrint.colon ^^ PPrint.blank 1 ^^ Fc.Type.to_doc s typ
            ^/^ PPrint.bang ^^ PPrint.blank 1 ^^ Fc.Type.to_doc s eff
            |> PPrint.group in
        PPrint.ToChannel.pretty 1.0 80 stdout (PPrint.hardline ^^ doc);
    end with
    | Typer.TypeError.TypeError (pos, err) ->
        flush stdout;
        PPrint.ToChannel.pretty 1.0 80 stderr
            (PPrint.hardline ^^ Typer.TypeError.to_doc (Typer.Env.current_uv_subst tenv) pos err ^^ PPrint.hardline);
        flush stderr);
    tenv

let rep tenv input =
    try
        let stmts = Parse.parse_commands_exn input in
        let doc = PPrint.group (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) Ast.Term.Stmt.to_doc
            (Vector.to_list stmts)) in
        PPrint.ToChannel.pretty 1.0 80 stdout doc;
        print_newline ();

        let tenv = Vector.fold_left ep tenv stmts in
        print_newline ();
        tenv
    with
        | SedlexMenhir.ParseError err ->
            prerr_endline (SedlexMenhir.string_of_ParseError err);
            tenv

let repl () =
    let rec loop tenv =
        match LNoise.linenoise prompt with
        | None -> ()
        | Some input ->
            let _ = LNoise.history_add input in
            let tenv = rep tenv input in
            loop tenv in
    print_endline (name_c ^ " prototype REPL. Press Ctrl+D (on *nix, Ctrl+Z on Windows) to quit.");
    loop (Typer.Env.interactive ())

let eval_t =
    let doc = "evaluate statements" in
    let expr =
        let docv = "STATEMENTS" in
        let doc = "the statements to evaluate" in
        C.Arg.(value & pos 0 string "" & info [] ~docv ~doc) in
    (C.Term.(const ignore $ (const rep $ (const Typer.Env.eval $ const ()) $ expr)), C.Term.info "eval" ~doc)

let repl_t =
    let doc = "interactive evaluation loop" in
    (C.Term.(const repl $ const ()), C.Term.info "repl" ~doc)

let default_t =
    let doc = "effective, modular, functional programming language. WIP." in
    (C.Term.(ret (const (fun () -> `Help (`Pager, None)) $ const ())), C.Term.info name ~doc)

let () =
    Hashtbl.randomize ();
    C.Term.exit (C.Term.eval_choice default_t [repl_t; eval_t])

