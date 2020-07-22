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

let%test_unit "parse_int" = try_roundtrip "do 23"

let%test_unit "parse_use" = try_roundtrip "do foo"

let%test_unit "parse_app" = try_roundtrip "do foo bar"

let%test_unit "parse_let" =
    try_roundtrip "do let x = 23; do x end";
    try_prints_as "do let x = 23; do begin y = 17; do y end end"
        "do let x = 23; begin y = 17; do y end"

let%test_unit "parse_ann" = try_roundtrip "do foo : int"

let%test_unit "parse_begin" =
    try_roundtrip "do begin x = 23; do x end";
    try_prints_as "do begin x = 23; do let y = 17; do y end end"
        "do begin x = 23; let y = 17; do y end"

let%test_unit "parse_record" =
    try_roundtrip "do {}";
    try_roundtrip "do {... foo with x = 23}";
    try_prints_as "do {... {} with x = 23}" "do {with x = 23}";
    try_prints_as "do {... {foo with x = 23} with y = 17}" "do {... foo with x = 23, y = 17}";
    try_prints_as "do {... {{} with x = 23} with y = 17}" "do {x = 23, y = 17}"

let%test_unit "parse_record_type" =
    try_roundtrip "do {||}";
    try_roundtrip "do {|... foo with x : int|}";
    try_prints_as "do {|... (||) with x : int|}" "do {|with x : int|}";
    try_prints_as "do {|... (|... foo with x : int|) with y : int|}" "do {|... foo with x : int, y : int|}";
    try_prints_as "do {|... (|... (||) with x : int|) with y : int|}" "do {|x : int, y : int|}" 

