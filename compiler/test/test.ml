open Broom_lib

let (^^) = PPrint.(^^)

let try_parse s =
    try Parse.parse_stmts_exn s with
    | SedlexMenhir.ParseError err -> failwith (SedlexMenhir.string_of_ParseError err)

let try_prints_as goal s =
    let stmts = try_parse s in
    let s' = PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) Ast.Term.Stmt.to_doc
        (Vector.to_list stmts)
        |> Util.doc_to_string in
    if s' = goal
    then ()
    else failwith (s' ^ "` != `" ^ goal)

let try_roundtrip s = try_prints_as s (Sedlexing.Utf8.from_string s)

let%test_unit "parse_int" = try_roundtrip "23"

let%test_unit "parse_use" = try_roundtrip "foo"

let%test_unit "parse_app" = try_roundtrip "foo bar"

let%test_unit "parse_let" =
    try_roundtrip "let {x = 23} x";
    try_roundtrip "let {x = 23} begin {y = 17} y"

let%test_unit "parse_ann" = try_roundtrip "foo : int"

let%test_unit "parse_begin" =
    try_roundtrip "begin {x = 23} x";
    try_roundtrip "begin {x = 23} let {y = 17} y"

let%test_unit "parse_record" =
    try_roundtrip "{}";
    try_roundtrip "{x = 23}";
    try_roundtrip "{x = 23; y = 17}";
    try_roundtrip "foo with {x = 23}";
    try_roundtrip "foo with {x = 23; y = 17}"

let%test_unit "parse_record_type" =
    try_roundtrip "{:}";
    try_roundtrip "{:x : int}";
    try_roundtrip "{:x : int; y : int}";
    try_roundtrip "foo with {:x : int}";
    try_roundtrip "foo with {:x : int; y : int}"

