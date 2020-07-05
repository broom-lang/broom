let (^^) = PPrint.(^^)

let prompt = "R1ML> "

let rec repl () =
    match LNoise.linenoise prompt with
    | None -> ()
    | Some input ->
        let _ = LNoise.history_add input in
        let lexbuf = SedlexMenhir.create_lexbuf (Sedlexing.Utf8.from_string input) in
        (try
            let stmts = SedlexMenhir.sedlex_with_menhir Lexer.token Parser.stmts lexbuf in
            let doc = PPrint.group (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) Ast.stmt_to_doc stmts) in
            PPrint.ToChannel.pretty 1.0 80 stdout doc;
            print_newline ()
        with
            | SedlexMenhir.ParseError err ->
                prerr_endline (SedlexMenhir.string_of_ParseError err));
        repl ()

let () =
    Hashtbl.randomize ();
    print_endline "R1ML prototype REPL. Press Ctrl+D (on *nix, Ctrl+Z on Windows) to quit.";
    repl ()

