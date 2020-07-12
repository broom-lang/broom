let try_parse s =
    try
        ignore (Broom_lib.Parse.parse_string_exn s)
    with
    | Broom_lib.SedlexMenhir.ParseError err ->
        failwith (Broom_lib.SedlexMenhir.string_of_ParseError err)

let%test_unit "parse_int" = try_parse "23"

