structure Parser : sig
    type config = {debug: bool, instream: TextIO.instream, name: string}
    val parse : config -> unit
end = struct
  structure BroomLrVals = BroomLrValsFun(structure Token = LrParser.Token)

  structure BroomLex = BroomLexFun(structure Tokens = BroomLrVals.Tokens)

  structure BroomParser = JoinWithArg(structure LrParser = LrParser
                                      structure ParserData = BroomLrVals.ParserData
                                      structure Lex = BroomLex)

  structure TC = TypecheckingCst

  fun logger debug str = if debug then TextIO.output(TextIO.stdOut, str) else ()

  fun invoke lexstream =
      let fun print_error (s, i, _) =
              TextIO.output(TextIO.stdOut,
                            "Error, line " ^ (Pos.toString i) ^ ", " ^ s ^ "\n")
      in  BroomParser.parse(0, lexstream, print_error, ())
      end

  type config = {debug: bool, instream: TextIO.instream, name: string}

  fun parse ({debug, instream, name}: config): unit =
      let val log = logger debug
          val lexer = BroomParser.makeLexer (fn _ => (case TextIO.inputLine instream
                                                      of SOME s => s
                                                       | _ => ""))
                                            (Pos.default name)
          val dummyEOF = BroomLrVals.Tokens.EOF(Pos.default name, Pos.default name)
          fun loop lexer =
              let val (program,lexer) = invoke lexer
                  val (nextToken,lexer) = BroomParser.Stream.get lexer
                  val _ = log (FixedCst.Term.exprToString program ^ "\n")
                  
                  val _ = log "===\n"

                  val (program, rootScope) = EnterTypechecker.toTypechecking program
                  val _ = Typechecker.elaborateExpr (TC.ExprScope rootScope) program

                  val program = ExitTypechecker.toF program
                  val _ = log (FixedFAst.Term.exprToString program ^ "\n")
              in if BroomParser.sameToken(nextToken,dummyEOF)
                 then ()
                 else loop lexer
              end
              handle Typechecker.TypeError err =>
                      TextIO.output (TextIO.stdErr, Typechecker.typeErrorToString err ^ ".\n")
       in loop lexer
      end
end
