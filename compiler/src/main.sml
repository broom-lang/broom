structure Main :> sig
    val main: string list -> unit
end = struct
    datatype flag_arity = datatype CLIParser.flag_arity

    val argSpecs =
        List.foldl CLIParser.FlagSpecs.insert' CLIParser.FlagSpecs.empty
                   [ ("debug", Nullary)
                   , ("lint", Nullary) ]
    val parser = CLIParser.parser argSpecs

    fun parseArgs argv =
        Either.map (fn (flaggeds, positionals) =>
                        let val (instream, name) = case positionals
                                                   of [] => (TextIO.stdIn, "<stdin>")
                                                    | [filename] => (TextIO.openIn filename, filename)
                        in { debug = isSome (CLIParser.Flaggeds.find (flaggeds, "debug"))
                           , lint = isSome (CLIParser.Flaggeds.find (flaggeds, "lint"))
                           , instream = instream
                           , name = name }
                        end)
                   (parser argv)

    fun main args =
        case parseArgs args
        of Either.Right params => Parser.parse params
         | Either.Left errors => List.app (fn error => print (error ^ "\n")) errors
end

val _ = Main.main (CommandLine.arguments ())

