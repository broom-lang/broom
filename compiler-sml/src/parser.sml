structure Parser : sig
    val parse : unit -> unit
end = struct
  structure BroomLrVals = BroomLrValsFun(structure Token = LrParser.Token)

  structure BroomLex = BroomLexFun(structure Tokens = BroomLrVals.Tokens)

  structure BroomParser = Join(structure LrParser = LrParser
                               structure ParserData = BroomLrVals.ParserData
                               structure Lex = BroomLex)

  fun invoke lexstream =
      let fun print_error (s,i:int,_) =
              TextIO.output(TextIO.stdOut,
                            "Error, line " ^ (Int.toString i) ^ ", " ^ s ^ "\n")
      in  BroomParser.parse(0,lexstream,print_error,())
      end

  fun parse () =
      let val lexer = BroomParser.makeLexer (fn _ => (case TextIO.inputLine TextIO.stdIn
                                                      of SOME s => s
                                                       | _ => ""))
          val dummyEOF = BroomLrVals.Tokens.EOF(0,0)
          val dummySEMI = BroomLrVals.Tokens.SEMI(0,0)
          fun loop lexer =
              let val (result,lexer) = invoke lexer
                  val (nextToken,lexer) = BroomParser.Stream.get lexer
                  val _ = case result
                          of SOME r =>
                              TextIO.output(TextIO.stdOut, "result = " ^ (Int.toString r) ^ "\n")
                           | NONE => ()
              in  if BroomParser.sameToken(nextToken,dummyEOF) then ()
                  else loop lexer
              end
       in loop lexer
      end
end
