val main =
    fn [] => Parser.parse false {instream = TextIO.stdIn, name = "<stdin>"}
     | ["--debug"] => Parser.parse true {instream = TextIO.stdIn, name = "<stdin>"}

val _ = main (CommandLine.arguments ())

