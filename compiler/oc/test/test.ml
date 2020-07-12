open Broom_lib

let (^^) = PPrint.(^^)

let try_parse s =
    try Parse.parse_string_exn s with
    | SedlexMenhir.ParseError err -> failwith (SedlexMenhir.string_of_ParseError err)

let try_prints_as goal s =
    let stmts = try_parse s in
    let s' = PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) Ast.Term.stmt_to_doc
        (Vector.to_list stmts)
        |> Util.doc_to_string in
    if s' = goal
    then ()
    else failwith (s' ^ "` != `" ^ goal)

let try_roundtrip s = try_prints_as s s

let%test_unit "parse_int" = try_roundtrip "23"

let%test_unit "parse_use" = try_roundtrip "foo"

let%test_unit "parse_app" = try_roundtrip "foo bar"

let%test_unit "parse_begin" =
    try_prints_as "23" "begin 23 end";
    try_roundtrip "begin val x = 23; x end";
    try_prints_as "begin val t = type int; val x = 23; x end"
        "begin type t = int; val x = 23; x end"

let%test_unit "parse_ann" = try_roundtrip "foo : int"

let%test_unit "parse_do" =
    try_roundtrip "do end";
    try_roundtrip "do 23 end";
    try_roundtrip "do val x = 23; x end";
    try_prints_as "do val t = type int; val x = 23; x end"
        "do type t = int; val x = 23; x end"

let%test_unit "parse_record" =
    try_roundtrip "{}";
    try_roundtrip "{foo with x = 23}";
    try_prints_as "{{} with x = 23}" "{with x = 23}";
    try_prints_as "{{foo with x = 23} with y = 17}" "{foo with x = 23, y = 17}";
    try_prints_as "{{{} with x = 23} with y = 17}" "{x = 23, y = 17}"

