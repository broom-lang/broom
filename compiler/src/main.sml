structure Main :> sig
    val main: string list -> unit
end = struct
    datatype flag_arity = datatype CLIParser.flag_arity
    datatype input = datatype Parser.input
    exception TypeError = TypeError.TypeError

    fun lexstreamFromInStream instream n =
        if TextIO.endOfStream instream
        then ""
        else TextIO.inputN (instream, n)

    datatype command
        = Build of {debug: bool, lint: bool, input: input}

    val cmdSpecs =
        List.foldl CLIParser.FlagSpecs.insert' CLIParser.FlagSpecs.empty
                   [ ("build", List.foldl CLIParser.FlagSpecs.insert' CLIParser.FlagSpecs.empty
                                          [ ("debug", Nullary)
                                          , ("lint", Nullary) ]) ]
    val parser = CLIParser.subcommandsParser cmdSpecs

    fun parseArgs argv =
        Either.map (fn ("build", flaggeds, positionals) =>
                        Build { debug = isSome (CLIParser.Flaggeds.find (flaggeds, "debug"))
                              , lint = isSome (CLIParser.Flaggeds.find (flaggeds, "lint"))
                              , input = case positionals
                                        of [] => Console TextIO.stdIn
                                         | [filename] => File (TextIO.openIn filename, filename) })
                   (parser argv)

    fun logger debug str = if debug then TextIO.output(TextIO.stdOut, str) else ()

    fun build {debug, lint, input} =
        let val log = logger debug
            
            val program = Parser.parse input
            val _ = log (PPrint.pretty 80 (Cst.Term.exprToDoc program) ^ "\n")
          
            val _ = log "===\n"

            val (_, program) = Typechecker.elaborateExpr TypecheckingEnv.empty program
            val program = ExitTypechecker.exprToF program
            val _ = log (PPrint.pretty 80 (FixedFAst.Term.exprToDoc program) ^ "\n")
         in if lint
            then ignore (Either.unwrap (FAstTypechecker.typecheck program))
            else ()
         end
         handle TypeError err =>
                 TextIO.output (TextIO.stdErr, PPrint.pretty 80 (TypeError.toDoc err))

    fun main args =
        case parseArgs args
        of Either.Right cmd =>
            (case cmd
             of Build args => 
                 ( build args
                 ; case #input args
                   of File (instream, _) => TextIO.closeIn instream
                    | Console _ => () ))
         | Either.Left errors => List.app (fn error => print (error ^ ".\n")) errors
end

val _ = Main.main (CommandLine.arguments ())

