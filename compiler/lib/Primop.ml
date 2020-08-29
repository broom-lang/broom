module T = FcType.Type

type t =
    | IAdd | ISub | IMul
    | Int
    | Type

let of_string = function
    | "iadd" -> Some IAdd
    | "isub" -> Some ISub
    | "imul" -> Some IMul
    | "int" -> Some Int
    | "type" -> Some Type
    | _ -> None

let to_string op =
    let name = match op with
        | IAdd -> "iadd"
        | ISub -> "isub"
        | IMul -> "imul"
        | Int -> "int"
        | Type -> "type" in
    name

let to_doc op = PPrint.string (to_string op)

let typeof = function
    | IAdd | ISub | IMul ->
        ( Vector.empty (), Vector.of_list [(T.Hole, T.Prim Prim.Int); (T.Hole, T.Prim Prim.Int)]
        , T.EmptyRow, T.Prim Prim.Int )
    | Int ->
        (Vector.empty (), Vector.empty (), T.EmptyRow, T.Type (T.to_abs (Prim Prim.Int)))
    | Type ->
        ( Vector.empty (), Vector.empty (), T.EmptyRow
        , T.Type (T.Exists ( Vector.singleton T.TypeK
                           , TypeL (Bv {depth = 0; sibli = 0})
                           , Type (T.to_abs (Bv {depth = 1; sibli = 0})) )) )

