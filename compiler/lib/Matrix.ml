(* NOTE: Column-major layout *)

type 'a t = {elems : 'a Vector.t; rows : int; cols : int}

let of_col col = {elems = col; rows = Vector.length col; cols = 1}

let get ~row ~col {elems; rows; cols} =
    if row < rows && col < cols
    then Some (Vector.get elems (rows * col + row))
    else None

let col coli {elems; rows; cols} =
    if coli < cols
    then Some (Streaming.Source.make
        ~init: (fun () -> coli * rows)
        ~pull: (fun i ->
            if i < (coli + 1) * rows
            then Some (Vector.get elems i, i + 1)
            else None) ())
    else None

let row rowi {elems; rows; cols} =
    if rowi < rows
    then Some (Streaming.Source.make
        ~init: (fun () -> rowi)
        ~pull: (fun i ->
            if i < Vector.length elems
            then Some (Vector.get elems i, i + rows)
            else None) ())
    else None

