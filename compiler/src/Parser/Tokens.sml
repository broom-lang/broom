structure BroomTokens = struct
    datatype t
        = Begin of Pos.t
        | Do of Pos.t
        | Return of Pos.t
        | Module of Pos.t
        | Interface of Pos.t
        | End of Pos.t
        | Val of Pos.t
        | Fun of Pos.t
        | Match of Pos.t
        | Type of Pos.t
        | Pi of Pos.t
        | Eq of Pos.t
        | DArrow of Pos.t
        | Arrow of Pos.t
        | Bar of Pos.t
        | Amp of Pos.t
        | Dot of Pos.t
        | DDot of Pos.t
        | Colon of Pos.t
        | Comma of Pos.t
        | Semi of Pos.t
        | Newline of Pos.t
        | LParen of Pos.t
        | RParen of Pos.t
        | LBracket of Pos.t
        | RBracket of Pos.t
        | LBrace of Pos.t
        | RBrace of Pos.t
        | Meta of Pos.t * Name.t * Pos.t
        | Intrinsic of Pos.t * string * Pos.t
        | Id of Pos.t * Name.t * Pos.t
        | Int of Pos.t * int * Pos.t
        | Bool of Pos.t * bool

    type vector = t vector

    val startPos =
        fn Begin pos => pos
         | Do pos => pos
         | Return pos => pos
         | Module pos => pos
         | Interface pos => pos
         | End pos => pos
         | Val pos => pos
         | Fun pos => pos
         | Match pos => pos
         | Type pos => pos
         | Pi pos => pos
         | Eq pos => pos
         | DArrow pos => pos
         | Arrow pos => pos
         | Bar pos => pos
         | Amp pos => pos
         | Dot pos => pos
         | DDot pos => pos
         | Colon pos => pos
         | Comma pos => pos
         | Semi pos => pos
         | Newline pos => pos
         | LParen pos => pos
         | RParen pos => pos
         | LBracket pos => pos
         | RBracket pos => pos
         | LBrace pos => pos
         | RBrace pos => pos
         | Meta (pos, _, _) => pos
         | Intrinsic (pos, _, _) => pos
         | Id (pos, _, _) => pos
         | Int (pos, _, _) => pos
         | Bool (pos, _) => pos

    val toName =
        fn Id (_, name, _) => SOME name
         | _ => NONE

    val toInt =
        fn Int (_, n, _) => SOME n
         | _ => NONE

    val toBool =
        fn Bool (_, b) => SOME b
         | _ => NONE

    val toString =
        fn Begin _ => "begin"
         | Do _ => "do"
         | Return _ => "return"
         | Interface _ => "interface"
         | End _ => "end"
         | Val _ => "val"
         | Fun _ => "fun"
         | Match _ => "match"
         | Type _ => "type"
         | Pi _ => "pi"
         | Eq _ => "="
         | DArrow _ => "=>"
         | Arrow _ => "->"
         | Bar _ => "|"
         | Amp _ => "&"
         | Dot _ => "."
         | DDot _ => ".."
         | Colon _ => ":"
         | Comma _ => ","
         | Semi _ => ";"
         | Newline _ => "NEWLINE"
         | LParen _ => "("
         | RParen _ => ")"
         | LBracket _ => "["
         | RBracket _ => "]"
         | LBrace _ => "{"
         | RBrace _ => "}"
         | Meta (_, name, _) => "@" ^ Name.toString name
         | Intrinsic (_, name, _) => "__" ^ name
         | Id (_, name, _) => Name.toString name
         | Int (_, n, _) => Int.toString n (* HACK *)
         | Bool (_, b) => if b then "True" else "False"

    val lookaheadToString =
        fn SOME tok => toString tok
         | NONE => "EOF"
end

