open Broom_lib

let (^^) = PPrint.(^^)

let prompt = "Broom> "

let rec repl () =
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
        repl ()

let () =
    Hashtbl.randomize ();
    print_endline "Broom prototype REPL. Press Ctrl+D (on *nix, Ctrl+Z on Windows) to quit.";
    repl ()

