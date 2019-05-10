structure Pos :> sig
    type t = {file: string, index: int, line: int, col: int}

    val default: string -> t
    val next: t -> char -> t

    val toString: t -> string
end = struct
    type t = {file: string, index: int, line: int, col: int}

    fun default file = {file = file, index = 0, line = 1, col = 1}

    fun nextLine line = fn #"\n" => line + 1
                         | _ => line

    fun nextCol col = fn #"\n" => 1
                       | _ => col + 1

    fun next {file, index, line, col} c =
        {file = file, index = index + 1, line = nextLine line c, col = nextCol col c}

    fun toString {file, index = _, line, col} =
        file ^ " at " ^ Int.toString line ^ ":" ^ Int.toString col
end
