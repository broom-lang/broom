structure Main :> sig
    val main: string list -> unit
end = struct
    val op|> = Fn.|>
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val text = PPrint.text
    datatype flag_arity = datatype CLIParser.flag_arity
    datatype input = datatype Parser.input
    datatype stmt = datatype FixedFAst.Term.stmt
    exception TypeError = TypeError.TypeError

    fun lexstreamFromInStream instream n =
        if TextIO.endOfStream instream
        then ""
        else TextIO.inputN (instream, n)

    datatype command
        = Build of {debug: bool, lint: bool, input: input}
        | Repl

    val cmdSpecs =
        List.foldl CLIParser.FlagSpecs.insert' CLIParser.FlagSpecs.empty
                   [ ("build", List.foldl CLIParser.FlagSpecs.insert' CLIParser.FlagSpecs.empty
                                          [ ("debug", Nullary)
                                          , ("lint", Nullary) ])
                   , ("repl", CLIParser.FlagSpecs.empty)]

    val parser = CLIParser.subcommandsParser cmdSpecs

    fun parseArgs argv =
        Either.map (fn ("build", flaggeds, positionals) =>
                        Build { debug = isSome (CLIParser.Flaggeds.find (flaggeds, "debug"))
                              , lint = isSome (CLIParser.Flaggeds.find (flaggeds, "lint"))
                              , input = case positionals
                                        of [] => Console TextIO.stdIn
                                         | [filename] => File (TextIO.openIn filename, filename) }
                     | ("repl", _, _) => Repl)
                   (parser argv)

    fun printErr str = TextIO.output (TextIO.stdErr, str)

    fun logger debug str = if debug then TextIO.output (TextIO.stdOut, str) else ()

    fun build {debug, lint, input} =
        let val log = logger debug
            
            val program = Parser.parse input
            val _ = log (PPrint.pretty 80 (Cst.Term.stmtsToDoc program) ^ "\n")
          
            val _ = log "===\n"

            val (program, _) = Typechecker.elaborateProgram (TypecheckingEnv.default ()) program
            val program = ExitTypechecker.programToF program
            val _ = log (PPrint.pretty 80 (FixedFAst.Term.programToDoc program) ^ "\n")
         in if lint
            then case FAstTypechecker.typecheckProgram program
                 of SOME err => raise Fail "Lint failed"
                  | NONE => ()
            else ()
         end
         handle TypeError err => printErr (PPrint.pretty 80 (TypeError.toDoc err))

    val prompt = "broom> "

    fun rep (tenv, venv) line =
        let val stmts = Parser.parse (Console (TextIO.openString line))
            val (program, tenv) = Typechecker.elaborateProgram tenv stmts
            val {body = FixedFAst.Term.Let (_, stmts, _), ...} = ExitTypechecker.programToF program
        in Vector.app (fn stmt as (Val (_, {var, typ}, _)) =>
                           (case FAstEval.interpret venv stmt
                            of Either.Left err => printErr "Runtime error.\n"
                             | Either.Right v =>
                                print ( Name.toString var ^ " = "
                                      ^ FAstEval.Value.toString v ^ " : "
                                      ^ FixedFAst.Type.Concr.toString typ ^ "\n" ))
                        | stmt as (Expr _) =>
                           (case FAstEval.interpret venv stmt
                            of Either.Left err => printErr "Runtime error.\n"
                             | Either.Right _ => ()))
                      stmts
         ; (tenv, venv)
        end

    fun rtp tenv line =
        let val stmts = Parser.parse (Console (TextIO.openString line))
            val (program, tenv) = Typechecker.elaborateProgram tenv stmts
            val {body = FixedFAst.Term.Let (_, stmts, _), ...} = ExitTypechecker.programToF program
        in Vector.app (fn stmt as (Val _) =>
                           stmt |> FixedFAst.Term.stmtToDoc
                                |> PPrint.pretty 80 |> print
                        | stmt as (Expr expr) =>
                           FixedFAst.Term.stmtToDoc stmt <> text ":"
                               <+> (expr |> FixedFAst.Term.typeOf
                                         |> FixedFAst.Type.Concr.toDoc)
                               |> PPrint.pretty 80 |> print)
                      stmts
         ; tenv
        end

    fun repl () =
        let val topVals = FAstEval.newToplevel ()
            fun loop tenv venv =
                let val _ = print prompt
                in case TextIO.inputLine TextIO.stdIn
                   of SOME line =>
                       (let val (tenv, venv) =
                                if String.isPrefix ":t " line (* TODO: Allow leading whitespace. *)
                                then (rtp tenv (String.extract (line, 2, NONE)), venv)
                                else rep (tenv, venv) line
                        in loop tenv venv
                        end
                        handle Parser.ParseError => loop tenv venv
                             | TypeError err => 
                                ( printErr (PPrint.pretty 80 (TypeError.toDoc err))
                                ; loop tenv venv ))
                    | NONE => ()
                end
        in loop (TypecheckingEnv.default ()) (FAstEval.newToplevel ())
        end

    fun main args =
        case parseArgs args
        of Either.Right cmd =>
            (case cmd
             of Build args => 
                 ( build args
                 ; case #input args
                   of File (instream, _) => TextIO.closeIn instream
                    | Console _ => () )
              | Repl => repl ())
         | Either.Left errors => List.app (fn error => print (error ^ ".\n")) errors
end

val _ = Main.main (CommandLine.arguments ())

