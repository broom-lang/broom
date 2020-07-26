open Broom_lib
module C = Cmdliner

let (^^) = PPrint.(^^)

let name = "broom"
let name_c = String.capitalize_ascii name
let prompt = name ^ "> "

let repl () =
    let rec loop () =
        match LNoise.linenoise prompt with
        | None -> ()
        | Some input ->
            let _ = LNoise.history_add input in
            (try
                let stmts = Parse.parse_string_exn input in
                let doc = PPrint.group (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) Ast.Term.stmt_to_doc
                    (Vector.to_list stmts)) in
                PPrint.ToChannel.pretty 1.0 80 stdout doc;
                print_newline ()
            with
                | SedlexMenhir.ParseError err ->
                    prerr_endline (SedlexMenhir.string_of_ParseError err));
            loop () in
    print_endline (name_c ^ " prototype REPL. Press Ctrl+D (on *nix, Ctrl+Z on Windows) to quit.");
    loop ()

let repl_t =
    let doc = "interactive evaluation loop" in
    (C.Term.(const repl $ const ()), C.Term.info "repl" ~doc)

let default_t =
    let doc = "effective, modular, functional programming language. WIP." in
    (C.Term.(ret (const (fun () -> `Help (`Pager, None)) $ const ())), C.Term.info name ~doc)

let () =
    Hashtbl.randomize ();
    C.Term.exit (C.Term.eval_choice default_t [repl_t])

