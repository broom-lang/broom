(* NOTE: Column-major layout *)

open Streaming

type 'a t = {elems : 'a Vector.t; rows : int; cols : int}

let height (mat : 'a t) = mat.rows
let width (mat : 'a t) = mat.cols

let get ~row ~col {elems; rows; cols} =
    if row < rows && col < cols
    then Some (Vector.get elems (rows * col + row))
    else None

let transpose ({elems = _; rows; cols} as mat) =
    { elems = Stream.from (Source.count 0) |> Stream.take cols
        |> Stream.flat_map (fun coli ->
            Stream.from (Source.count 0) |> Stream.take rows
            |> Stream.map (fun rowi -> (rowi, coli)))
        |> Stream.map (fun (row, col) -> get ~row ~col mat |> Option.get)
        |> Stream.into (Sink.buffer (rows * cols))
        |> Vector.of_array_unsafe
    ; rows = cols; cols = rows }

let empty = {elems = Vector.empty; rows = 0; cols = 0}

let of_col col = {elems = col; rows = Vector.length col; cols = 1}

let of_cols colvecs =
    let colvecs = Stream.into (Vector.sink ()) colvecs in
    let cols = Vector.length colvecs in
    if cols > 0 then begin
        let rows = Vector.length (Vector.get colvecs 0) in
        { elems = Stream.from (Vector.to_source colvecs)
            |> Stream.flat_map (fun col -> Stream.from (Vector.to_source col))
            |> Stream.into (Sink.buffer (rows * cols))
            |> Vector.of_array_unsafe
        ; rows; cols }
    end else empty

let of_rows rowvecs = transpose (of_cols rowvecs) (* OPTIMIZE *)

let hcat = function
    | (mat :: _) as mats ->
        let rows = mat.rows in
        { elems = Stream.from (Source.list mats)
            |> Stream.flat_map (fun {elems; rows = rows'; cols = _} ->
                assert (rows' = rows);
                Stream.from (elems |> Vector.to_source))
            |> Stream.into (Vector.sink ())
        ; cols = List.fold_left (fun cols (mat : 'a t) -> cols + mat.cols) 0 mats
        ; rows }
    | [] -> empty

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

let sub_cols start len {elems; rows; cols} =
    if 0 <= start && start <= cols then begin
        let len = Option.value len ~default: (cols - start) in
        if 0 <= len && len <= cols - start
        then { elems = Vector.sub elems (start * rows) (len * rows)
            ; cols = len; rows }
        else raise (Invalid_argument "Matrix.sub_cols: invalid len")
    end else raise (Invalid_argument ("Matrix.sub_cols: invalid index "
        ^ "0 < " ^ Int.to_string start ^ " <= " ^ Int.to_string cols))

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

