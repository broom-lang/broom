val main =
    fn [] => Parser.parse false
     | ["--debug"] => Parser.parse true

val _ = main (CommandLine.arguments ())

