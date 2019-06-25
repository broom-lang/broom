structure Parser : sig
    datatype input
        = File of TextIO.instream * string
        | Console of TextIO.instream

    val parse: input -> Cst.Term.expr
end = struct
    structure BroomLrVals = BroomLrValsFun(structure Token = LrParser.Token)

    structure BroomLex = BroomLexFun(structure Tokens = BroomLrVals.Tokens)

    structure BroomParser = JoinWithArg(structure LrParser = LrParser
                                      structure ParserData = BroomLrVals.ParserData
                                      structure Lex = BroomLex)

    fun lexstreamFromInStream instream n =
        if TextIO.endOfStream instream
        then ""
        else TextIO.inputN (instream, n)

    datatype input
        = File of TextIO.instream * string
        | Console of TextIO.instream

    fun printError (msg, pos, _) =
        TextIO.output(TextIO.stdOut, "Error, line " ^ (Pos.toString pos) ^ ", " ^ msg ^ "\n")

    val parse =
        fn File (instream, filename) =>
            let val lexer = BroomParser.makeLexer (lexstreamFromInStream instream) (Pos.default filename)
            in #1 (BroomParser.parse (15, lexer, printError, ()))
            end
         | Console instream =>
            let val lexer = BroomParser.makeLexer (lexstreamFromInStream instream) (Pos.default "<stdin>")
            in #1 (BroomParser.parse (0, lexer, printError, ()))
            end
end
