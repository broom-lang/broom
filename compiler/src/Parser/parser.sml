structure Parser : sig
    type input = {instream: TextIO.instream, sourcemap: Pos.sourcemap}

    type repair = BroomTokens.token AntlrRepair.repair
    val repairToString : Pos.sourcemap -> repair -> string

    val parse: input -> ( Cst.Term.stmt vector option * repair list
                        , Cst.Term.stmt vector ) Either.t
end = struct
    structure BroomParser = BroomParseFn(BroomLexer)

    type input = {instream: TextIO.instream, sourcemap: Pos.sourcemap}
        
    type repair = BroomTokens.token AntlrRepair.repair

    val repairToString = AntlrRepair.repairToString BroomTokens.toString

    fun parse {instream, sourcemap} =
        let val tokenStream = BroomLexer.streamifyInstream instream
            val lex = BroomLexer.lex sourcemap
        in  case BroomParser.parse lex tokenStream
            of (SOME stmts, _, []) => Either.Right stmts
             | (optStmts, _, repairs) => Either.Left (optStmts, repairs)
        end
end
