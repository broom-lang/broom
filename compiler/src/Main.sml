structure Main :> sig
    val main: string * string list -> OS.Process.status
end = struct
    val op|> = Fn.|>
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val text = PPrint.text
    datatype either = datatype Either.t
    datatype flag_arity = datatype CLIParser.flag_arity
    type input = Parser.input
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
                                        of [] => { instream = TextIO.stdIn
                                                 , sourcemap = Pos.mkSourcemap () }
                                         | [filename] => { instream = TextIO.openIn filename
                                                         , sourcemap = Pos.mkSourcemap' filename }
                                         | _ => raise Fail "Multiple input files unimplemented" }
                     | ("repl", _, _) => Repl
                     | (cmd, _, _) => raise Fail ("Unreachable code; unknown subcommand " ^ cmd))
                   (parser argv)

    fun printErr str = TextIO.output (TextIO.stdErr, str)

    fun logger debug str = if debug then TextIO.output (TextIO.stdOut, str) else ()

    fun build {debug, lint, input = input as {sourcemap, instream = _}} =
        let val log = logger debug
        in  case Parser.parse input
            of Right program =>
                let val _ = log (PPrint.pretty 80 (Cst.Term.beginToDoc program) ^ "\n")
                    val _ = log "===\n\n"
                    val tenv = TypecheckingEnv.default sourcemap
                in case Typechecker.elaborateProgram tenv program
                   of Right (program, _) =>
                       let val program = ExitTypechecker.programToF tenv program
                           do if lint
                              then case FAstTypechecker.typecheckProgram program
                                   of SOME err => raise Fail "Lint failed"
                                   | NONE => ()
                              else ()
                       in  case WellFounded.elaborate program
                           of Right program =>
                               ( log (PPrint.pretty 80 (FixedFAst.Term.programToDoc () program) ^ "\n")
                               ; log "===\n\n"
                               ; if lint
                                 then case FAstTypechecker.typecheckProgram program
                                      of SOME err => raise Fail "Lint failed"
                                       | NONE => ()
                                 else ()
                               ; let val program = PatternMatching.implement program
                                     do if lint
                                        then case FAstTypechecker.typecheckProgram program
                                             of SOME err => raise Fail "Lint failed"
                                              | NONE => ()
                                        else ()
                                     val program = X64SysVCpsConvert.cpsConvert program
                                     val _ = log (PPrint.pretty 80 (Cps.Program.toDoc program) ^ "\n")
                                     do log "===\n\n"
                                     do if lint
                                        then case CpsTypechecker.checkProgram program
                                             of Right () => ()
                                              | Left err => raise Fail "CPS lint failed"
                                        else ()
                                     val program = ClosureConvert.convert program
                                     val _ = log (PPrint.pretty 80 (Cps.Program.toDoc program) ^ "\n")
                                     do log "===\n\n"
                                     do if lint
                                        then case CpsTypechecker.checkProgram program
                                             of Right () => ()
                                              | Left err => raise Fail (PPrint.pretty 80 (CpsTypechecker.errorToDoc err))
                                        else ()
                                    val program = X64InstrSelection.selectInstructions program
                                    do log (PPrint.pretty 80 (X64Isa.Program.toDoc program) ^ "\n")
                                    do log "===\n\n"
                                    val program = X64ScheduleParams.schedule program
                                    do log (PPrint.pretty 80 (X64Isa.Program.toDoc program) ^ "\n")
                                    do log "===\n\n"
                                    val allocated as {program, ...} = X64SysVRegisterAllocation.allocate program
                                    do log (PPrint.pretty 80 (X64RegIsa.Program.toDoc program) ^ "\n")
                                    do log "===\n\n"
                                    val program = X64Logues.insert allocated
                                    do log (PPrint.pretty 80 (X64RegIsa.Program.toDoc program) ^ "\n")
                                    do log "===\n\n"
                                    val program = X64Linearize.linearize program
                                    do log (PPrint.pretty 80 (X64SeqIsa.Program.toDoc program) ^ "\n")
                                    do log "===\n\n"
                                 in GasX64SysVAbiEmit.emit TextIO.stdOut program
                                  ; OS.Process.success
                                 end )
                            | Left errors =>
                               ( Vector.app (printErr o PPrint.pretty 80 o WellFounded.errorToDoc sourcemap)
                                            errors
                               ; OS.Process.failure )
                       end
                    | Left (program, _, errors) =>
                       ( List.app (fn err => printErr (PPrint.pretty 80 (TypeError.toDoc tenv err)))
                                  errors
                       ; OS.Process.failure )
                end
             | Left (_, repairs) =>
                ( List.app (fn repair => printErr (Parser.repairToString sourcemap repair ^ "\n"))
                           repairs
                ; OS.Process.failure )
        end

    val prompt = "broom> "

    fun rep (tenv, venv) line =
        let val input as {sourcemap, ...} =
                {instream = TextIO.openString line, sourcemap = Pos.mkSourcemap ()}
        in  case Parser.parse input
            of Right stmts =>
                (case Typechecker.elaborateProgram tenv stmts
                 of Right (program, tenv) =>
                     let val program = ExitTypechecker.programToF tenv program
                     in  case WellFounded.elaborate program
                         of Right program =>
                             let val program as {code = (_, stmts, _), ...} = PatternMatching.implement program
                             in Vector1.app (fn stmt as (Val (_, {var, typ, ...}, _)) =>
                                                let val v = FAstEval.interpret venv stmt
                                                in print ( Name.toString var ^ " = "
                                                         ^ FAstEval.Value.toString v ^ " : "
                                                         ^ FixedFAst.Type.Concr.toString () typ ^ "\n" )
                                                end
                                              | stmt as (Expr _) => ignore (FAstEval.interpret venv stmt))
                                           stmts
                              ; (tenv, venv)
                             end
                          | Left errors =>
                             ( Vector.app (printErr o PPrint.pretty 80 o WellFounded.errorToDoc sourcemap)
                                          errors
                             ; (tenv, venv) )
                     end
                  | Left (_, _, errors) =>
                     ( List.app (fn err => printErr (PPrint.pretty 80 (TypeError.toDoc tenv err)))
                                errors
                     ; (tenv, venv) ))
             | Left (_, repairs) =>
                ( List.app (fn repair => printErr (Parser.repairToString sourcemap repair ^ "\n"))
                           repairs
                ; (tenv, venv) )
        end

    fun rtp tenv line =
        let val input as {sourcemap, ...} =
                {instream = TextIO.openString line, sourcemap = Pos.mkSourcemap ()}
        in  case Parser.parse input
            of Right stmts =>
                (case Typechecker.elaborateProgram tenv stmts
                 of Right (program, tenv) =>
                     let val program = ExitTypechecker.programToF tenv program
                     in  case WellFounded.elaborate program
                         of Right program =>
                             ( print (PPrint.pretty 80 (FixedFAst.Term.programToDoc () program))
                             ; tenv )
                          | Left errors =>
                             ( Vector.app (printErr o PPrint.pretty 80 o WellFounded.errorToDoc sourcemap)
                                          errors
                             ; tenv )
                     end
                  | Left (_, _, errors) =>
                     ( List.app (fn err => printErr (PPrint.pretty 80 (TypeError.toDoc tenv err)))
                                errors
                     ; tenv ))
             | Left (_, repairs) =>
                ( List.app (fn repair => printErr (Parser.repairToString sourcemap repair ^ "\n"))
                           repairs
                ; tenv )
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
                        (* FIXME: 
                        handle Parser.ParseError => loop tenv venv
                             | TypeError err => 
                                ( printErr (PPrint.pretty 80 (TypeError.toDoc err))
                                ; loop tenv venv ) *))
                    | NONE => ()
                end
        in loop (TypecheckingEnv.default (AntlrStreamPos.mkSourcemap ())) (FAstEval.newToplevel ())
        end

    fun main (name, args) =
        (case parseArgs args
         of Either.Right cmd =>
             (case cmd
              of Build args => 
                  let val status = build args
                  in TextIO.closeIn (#instream (#input args))
                   ; status
                  end
               | Repl =>
                  ( repl ()
                  ; OS.Process.success ))
          | Either.Left errors =>
             ( List.app (fn error => print (error ^ ".\n")) errors
             ; OS.Process.failure ))
        handle exn =>
            ( print ("unhandled exception: " ^ exnMessage exn ^ "\n")
            ; List.app (fn s => print ("\t" ^ s ^ "\n")) (SMLofNJ.exnHistory exn)
            ; OS.Process.failure )
end

