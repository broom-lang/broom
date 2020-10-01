(* NOTE: Column-major layout *)

open Streaming

type 'a t = {elems : 'a Vector.t; rows : int; cols : int}

let of_col col = {elems = col; rows = Vector.length col; cols = 1}

let height (mat : 'a t) = mat.rows
let width (mat : 'a t) = mat.cols

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

let row rowi {elems; rows; cols = _} =
    if rowi < rows
    then Some (Streaming.Source.make
        ~init: (fun () -> rowi)
        ~pull: (fun i ->
            if i < Vector.length elems
            then Some (Vector.get elems i, i + rows)
            else None) ())
    else None

let remove_col coli {elems; rows; cols} =
    let cols' = cols - 1 in
    { elems = Stream.concat
            (Stream.take (coli * rows) (Stream.from (Vector.to_source elems)))
            (Stream.drop ((coli + 1) * rows) (Stream.from (Vector.to_source elems)))
        |> Stream.into (Sink.buffer (cols' * rows))
        |> Vector.of_array_unsafe
    ; cols = cols'; rows }

let select_rows rowis {elems; rows = _; cols} =
    let rows' = IntSet.cardinal rowis in
    { elems = Stream.from (Source.seq (IntSet.to_seq rowis))
        |> Stream.cycle ~times: cols
        |> Stream.map (Vector.get elems)
        |> Stream.into (Sink.buffer (cols * rows'))
        |> Vector.of_array_unsafe
    ; rows = rows'; cols }

