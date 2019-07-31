structure BroomTokens = struct
    datatype t
        = Do of Pos.t
        | Module of Pos.t
        | Interface of Pos.t
        | End of Pos.t
        | Val of Pos.t
        | Fun of Pos.t
        | Type of Pos.t
        | If of Pos.t
        | Then of Pos.t
        | Else of Pos.t
        | Eq of Pos.t
        | DArrow of Pos.t
        | Arrow of Pos.t
        | Bar of Pos.t
        | Amp of Pos.t
        | Dot of Pos.t
        | DDot of Pos.t
        | Colon of Pos.t
        | Comma of Pos.t
        | LParen of Pos.t
        | RParen of Pos.t
        | LBracket of Pos.t
        | RBracket of Pos.t
        | LBrace of Pos.t
        | RBrace of Pos.t
        | Id of Pos.t * Name.t * Pos.t
        | Int of Pos.t * int * Pos.t
        | Bool of Pos.t * bool
end

