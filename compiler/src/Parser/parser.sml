structure Parser : sig
    datatype input
        = File of TextIO.instream * string
        | Console of TextIO.instream

    val parse: input -> Cst.Term.stmt vector
end = struct
    (* TODO: Move this boilerplate to Nipo lib: *)
    structure TextIOInput = NipoStreamIOInput(struct
        structure IOStream = TextIO.StreamIO
        structure Token = CharToken
    end)

    structure LexerTextInput = LexerInput(TextIOInput)
    structure Lexer = BroomLexer(struct
        structure Input = LexerTextInput
        structure Token = BroomTokens
    end)
    structure TokenStream = NipoLexedInput(Lexer)

    structure BroomParser = BroomParser(TokenStream)

    fun lexstreamFromInStream instream filename = let
        val input = TextIO.getInstream instream
        val input = TextIOInput.fromInstream input
        val input = LexerTextInput.fromInner (input, Pos.default filename)
        in TokenStream.tokenize input
    end

    datatype input
        = File of TextIO.instream * string
        | Console of TextIO.instream

    fun printError (msg, pos, _) =
        TextIO.output(TextIO.stdOut, "Error, line " ^ (Pos.toString pos) ^ ", " ^ msg ^ "\n")

    val parse =
        fn File (instream, filename) => BroomParser.start__program (lexstreamFromInStream instream filename)
         | Console instream => BroomParser.start__program (lexstreamFromInStream instream "STDIN")
end
