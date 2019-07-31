functor NipoLexer(Args: sig
    structure Input: NIPO_LEXER_INPUT
    structure Token: NIPO_POSITIONED_TOKEN where type t = NipoTokens.t
end) :> NIPO_LEXER
    where type Input.stream = Args.Input.stream
    where type Input.checkpoint = Args.Input.checkpoint
    where type Token.t = NipoTokens.t
= struct
    structure Input = Args.Input
    structure Token = Args.Token

    fun match token input =
        case Input.pop input
        of SOME token' =>
            if token' = token
            then token'
            else raise Fail ( "expected " ^ Input.Token.toString token
                            ^ ", got " ^ Input.Token.toString token'
                            ^ " at " ^ Input.Pos.toString (Input.pos input) )
         | NONE =>
            raise Fail ( "expected " ^ Input.Token.toString token
                       ^ ", got " ^ Input.Token.lookaheadToString NONE
                       ^ " at " ^ Input.Pos.toString (Input.pos input) )


    fun matchPred pred input =
        case Input.pop input
        of SOME token' =>
            if pred token'
            then token'
            else raise Fail ( "unexpected " ^ Input.Token.toString token'
                            ^ " at " ^ Input.Pos.toString (Input.pos input) )
         | NONE =>
            raise Fail ( "unexpected " ^ Input.Token.lookaheadToString NONE                       ^ " at " ^ Input.Pos.toString (Input.pos input) )


    and tok input =
        case Input.peek input
        of SOME (#"=") =>
            let val _ = match (#"=") input
                val _ = case Input.peek input
            of SOME (#">") =>
                let val optional0 = match (#">") input
                in ()
                end
             | lookahead =>
                ()
            in 0
            end
         | SOME (#"-") =>
            let val _ = match (#"-") input
                val _ = match (#">") input
            in 1
            end
         | SOME (#"|") =>
            let val _ = match (#"|") input
            in 2
            end
         | SOME (#"&") =>
            let val _ = match (#"&") input
            in 3
            end
         | SOME (#".") =>
            let val _ = match (#".") input
                val _ = case Input.peek input
            of SOME (#".") =>
                let val optional1 = match (#".") input
                in ()
                end
             | lookahead =>
                ()
            in 4
            end
         | SOME (#":") =>
            let val _ = match (#":") input
            in 5
            end
         | SOME (#",") =>
            let val _ = match (#",") input
            in 6
            end
         | SOME (#"(") =>
            let val _ = match (#"(") input
            in 7
            end
         | SOME (#")") =>
            let val _ = match (#")") input
            in 8
            end
         | SOME (#"[") =>
            let val _ = match (#"[") input
            in 9
            end
         | SOME (#"]") =>
            let val _ = match (#"]") input
            in 10
            end
         | SOME (#"{") =>
            let val _ = match (#"{") input
            in 11
            end
         | SOME (#"}") =>
            let val _ = match (#"}") input
            in 12
            end
         | lookahead =>
            if lookahead = SOME (#"_") orelse isSome lookahead andalso Char.isAlpha (valOf lookahead) then
                let val _ = let fun loop2 inner =
                        let val elem3 = case Input.peek input
                            of SOME (#"_") =>
                                let val _ = match (#"_") input
                                in ()
                                end
                             | lookahead =>
                                if isSome lookahead andalso Char.isAlpha (valOf lookahead) then
                                    let val _ = matchPred (fn lookahead => Char.isAlpha lookahead) input
                                    in ()
                                    end
                                else
                                    raise Fail ("unexpected " ^ Input.Token.lookaheadToString lookahead ^ " in tok at " ^ Input.Pos.toString (Input.pos input))
                        in  let val lookahead = Input.peek input
                            in  if lookahead = SOME (#"_") orelse isSome lookahead andalso Char.isAlpha (valOf lookahead) then
                                    let val elems4 = loop2 input
                                    in ()
                                    end
                                else
                                    ()
                            end
                        end
                in loop2 input
                end
                in 13
                end
            else
                if isSome lookahead andalso Char.isDigit (valOf lookahead) then
                    let val _ = let fun loop5 inner =
                            let val elem6 = matchPred (fn lookahead => Char.isDigit lookahead) input
                            in  let val lookahead = Input.peek input
                                in  if isSome lookahead andalso Char.isDigit (valOf lookahead) then
                                        let val elems7 = loop5 input
                                        in ()
                                        end
                                    else
                                        ()
                                end
                            end
                    in loop5 input
                    end
                    in 14
                    end
                else
                    raise Fail ("unexpected " ^ Input.Token.lookaheadToString lookahead ^ " in tok at " ^ Input.Pos.toString (Input.pos input))

    and ws input =
        let val lookahead = Input.peek input
        in  let val _ = let fun loop8 inner =
                    let val lookahead = Input.peek input
                    in  if isSome lookahead andalso Char.isSpace (valOf lookahead) then
                            let val elem9 = matchPred (fn lookahead => Char.isSpace lookahead) input
                                val elems10 = loop8 input
                            in ()
                            end
                        else
                            ()
                    end
            in loop8 input
            end
            in ()
            end
        end

    val actions =
        Vector.fromList [  fn (s, cs, _) =>
                     case String.size cs
                     of 1 => Eq s
                      | 2 => DArrow s
                      | _ => raise Fail "unreachable" 
                        ,  Arrow o #1 
                        ,  Bar o #1 
                        ,  Amp o #1 
                        ,  fn (s, cs, _) =>
                     case String.size cs
                     of 1 => Dot s
                      | 2 => DDot s
                      | _ => raise Fail "unreachable" 
                        ,  Colon o #1 
                        ,  Comma o #1 
                        ,  LParen o #1 
                        ,  RParen o #1 
                        ,  LBracket o #1 
                        ,  RBracket o #1 
                        ,  LBrace o #1 
                        ,  RBrace o #1 
                        ,  fn args as (s, cs, _) =>
                                 case cs
                                 of "val" => Val s
                                  | "type" => Type s
                                  | "do" => Do s
                                  | "module" => Module s
                                  | "interface" => Interface s
                                  | "fun" => Fun s
                                  | "end" => End s
                                  | "if" => If s
                                  | "then" => Then s
                                  | "else" => Else s
                                  | "True" => Bool (s, true)
                                  | "False" => Bool (s, false)
                                  | _ => Id args 
                        ,  fn (s, cs, e) => Int (s, valOf (Int.fromString cs), e)  ]

    fun next input =
        ( ws input
        ; Option.map (fn _ =>
                          let val startPos = Input.pos input
                              val startMark = Input.checkpoint input
                              val actionIndex = tok input
                              val endPos = Input.pos input
                              val endMark = Input.checkpoint input
                              val _ = Input.reset (input, startMark)
                              val len = #index endPos - #index startPos
                              (* Slightly breach abstraction to avoid recomputing `endPos`: *)
                             val recognizedPrefix = Input.Inner.inputN (Input.toInner input, len)
                             val _ = Input.reset (input, endMark)
                          in Vector.sub (actions, actionIndex) (startPos, recognizedPrefix, endPos)
                          end)
                     (Input.peek input) )
end
