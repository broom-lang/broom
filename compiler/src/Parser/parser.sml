structure Parser : sig
    val parse : bool -> unit
end = struct
  structure BroomLrVals = BroomLrValsFun(structure Token = LrParser.Token)

  structure BroomLex = BroomLexFun(structure Tokens = BroomLrVals.Tokens)

  structure BroomParser = JoinWithArg(structure LrParser = LrParser
                                      structure ParserData = BroomLrVals.ParserData
                                      structure Lex = BroomLex)

  structure CTerm = Cst.Term
  structure TC = TypecheckingCst

  fun logger debugLog str = if debugLog then TextIO.output(TextIO.stdOut, str) else ()

  fun invoke lexstream =
      let fun print_error (s, i, _) =
              TextIO.output(TextIO.stdOut,
                            "Error, line " ^ (Pos.toString i) ^ ", " ^ s ^ "\n")
      in  BroomParser.parse(0, lexstream, print_error, ())
      end

  fun parse debugLog =
      let val log = logger debugLog
          val lexer = BroomParser.makeLexer (fn _ => (case TextIO.inputLine TextIO.stdIn
                                                      of SOME s => s
                                                       | _ => ""))
                                            (Pos.default "<stdin>")
          val dummyEOF = BroomLrVals.Tokens.EOF(Pos.default "<stdin>", Pos.default "<stdin>")
          fun loop lexer =
              let val (program,lexer) = invoke lexer
                  val (nextToken,lexer) = BroomParser.Stream.get lexer
                  val _ = Vector.app (fn stmt => log (FixedCst.Term.stmtToString stmt ^ "\n"))
                                     program
                  val _ = log "===\n"
                  val pos = Pos.default "<stdin>"
                  val stmts = Vector.map Typechecker.injectStmt program
                  val vals = NameHashTable.mkTable (0, Subscript)
                  val _ = Vector.app (Typechecker.stmtBind vals) stmts
                  val expr = CTerm.Let ( pos, stmts
                                       , ref (TC.InputExpr (CTerm.Const (pos, Const.Int 0))))
                  val exprRef = ref (TC.InputExpr expr)
                  val scope = {parent = ref NONE, expr = exprRef, vals}
                  val _ = Typechecker.uplinkExprScopes NONE (ref (TC.ScopeExpr scope))
                  val _ = Typechecker.elaborateExpr (TC.ExprScope scope) exprRef
              in if BroomParser.sameToken(nextToken,dummyEOF)
                 then ()
                 else loop lexer
              end
       in loop lexer
      end
end
