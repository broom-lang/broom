structure Parser : sig
    type config = {debug: bool, lint: bool, instream: TextIO.instream, name: string}
    val parse : config -> unit
end = struct
  structure BroomLrVals = BroomLrValsFun(structure Token = LrParser.Token)

  structure BroomLex = BroomLexFun(structure Tokens = BroomLrVals.Tokens)

  structure BroomParser = JoinWithArg(structure LrParser = LrParser
                                      structure ParserData = BroomLrVals.ParserData
                                      structure Lex = BroomLex)

  structure TC = TypecheckingCst
  exception TypeError = TypeError.TypeError

  fun logger debug str = if debug then TextIO.output(TextIO.stdOut, str) else ()

  fun invoke lexstream =
      let fun print_error (s, i, _) =
              TextIO.output(TextIO.stdOut,
                            "Error, line " ^ (Pos.toString i) ^ ", " ^ s ^ "\n")
      in  BroomParser.parse(0, lexstream, print_error, ())
      end

  type config = {debug: bool, lint: bool, instream: TextIO.instream, name: string}

  fun parse ({debug, lint, instream, name}: config): unit =
      let val log = logger debug
          val lexer = BroomParser.makeLexer (fn _ => (case TextIO.inputLine instream
                                                      of SOME s => s
                                                       | _ => ""))
                                            (Pos.default name)
          val dummyEOF = BroomLrVals.Tokens.EOF(Pos.default name, Pos.default name)
          fun loop lexer =
              let val (program,lexer) = invoke lexer
                  val (nextToken,lexer) = BroomParser.Stream.get lexer
                  val _ = log (PPrint.pretty 80 (Cst.Term.exprToDoc program) ^ "\n")
                  
                  val _ = log "===\n"

                  val (_, program) = Typechecker.elaborateExpr TypecheckingEnv.empty program

                  val program = ExitTypechecker.exprToF program
                  val _ = log (PPrint.pretty 80 (FixedFAst.Term.exprToDoc program) ^ "\n")

                  val _ = if lint
                          then ignore (Either.unwrap (FAstTypechecker.typecheck program))
                          else ()
              in if BroomParser.sameToken(nextToken,dummyEOF)
                 then ()
                 else loop lexer
              end
              handle TypeError err =>
                      TextIO.output (TextIO.stdErr, PPrint.pretty 80 (TypeError.toDoc err))
       in loop lexer
      end
end
