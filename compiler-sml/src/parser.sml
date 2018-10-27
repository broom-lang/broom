structure Parser : sig
    val parse : unit -> unit
end = struct
  structure BroomLrVals = BroomLrValsFun(structure Token = LrParser.Token)

  structure BroomLex = BroomLexFun(structure Tokens = BroomLrVals.Tokens)

  structure BroomParser = JoinWithArg(structure LrParser = LrParser
                                      structure ParserData = BroomLrVals.ParserData
                                      structure Lex = BroomLex)

  fun invoke lexstream =
      let fun print_error (s, i, _) =
              TextIO.output(TextIO.stdOut,
                            "Error, line " ^ (Pos.toString i) ^ ", " ^ s ^ "\n")
      in  BroomParser.parse(0, lexstream, print_error, ())
      end

  fun parse () =
      let val lexer = BroomParser.makeLexer (fn _ => (case TextIO.inputLine TextIO.stdIn
                                                      of SOME s => s
                                                       | _ => ""))
                                            (Pos.default "<stdin>")
          val dummyEOF = BroomLrVals.Tokens.EOF(Pos.default "<stdin>", Pos.default "<stdin>")
          fun loop lexer =
              let val (result,lexer) = invoke lexer
                  val (nextToken,lexer) = BroomParser.Stream.get lexer
                  val _ = Vector.app (fn stmt => TextIO.output(TextIO.stdOut,
                                                               Cst.stmtToString stmt ^ "\n"))
                                     result
              in  if BroomParser.sameToken(nextToken,dummyEOF) then ()
                  else loop lexer
              end
       in loop lexer
      end
end
