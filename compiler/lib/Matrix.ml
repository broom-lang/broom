(* NOTE: Row-major layout *)

open Streaming

type 'a t = {elems : 'a Vector.t; width : int; height : int}

let height (mat : 'a t) = mat.width
let width (mat : 'a t) = mat.height

let get ~row ~col {elems; width; height} =
    if 0 <= row && row < height && 0 <= col && col < width
    then Some (Vector.get elems (width * row + col))
    else None

let empty = {elems = Vector.empty; width = 0; height = 0}

let of_col col = {elems = col; width = 1; height = Vector.length col}

let of_rows rowvecs =
    let rowvecs = Stream.into (Vector.sink ()) rowvecs in
    let height = Vector.length rowvecs in
    if height > 0 then begin
        let width = Vector.length (Vector.get rowvecs 0) in
        { elems = Stream.from (Vector.to_source rowvecs)
            |> Stream.flat_map (fun row ->
                assert (Vector.length row = width);
                Stream.from (Vector.to_source row))
            |> Stream.into (Sink.buffer (width * height))
            |> Vector.of_array_unsafe
        ; width; height }
    end else empty

let row rowi {elems; width; height} =
    if 0 <= rowi && rowi < height
    then Some (Streaming.Source.make
        ~init: (fun () -> rowi * width)
        ~pull: (fun i ->
            if i < (rowi + 1) * width 
            then Some (Vector.get elems i, i + 1)
            else None) ())
    else None

let col coli {elems; width; height} =
    if 0 <= coli && coli < width
    then Some (Streaming.Source.make
        ~init: (fun () -> coli)
        ~pull: (fun i ->
            if i < Vector.length elems
            then Some (Vector.get elems i, i + width)
            else None) ())
    else None

let hcat = function
    | (mat :: _) as mats ->
        let height = mat.height in
        let mats = Vector.of_list mats in
        let width = Vector.fold (fun w (mat : 'a t) -> w + mat.width) 0 mats in
        { elems =
            (let open Stream.Syntax in
            let* rowi = Stream.range 0 height in
            let* i = Stream.range 0 (Vector.length mats) in
            Stream.from (row rowi (Vector.get mats i) |> Option.get))
            |> Stream.into (Sink.buffer (width * height))
            |> Vector.of_array_unsafe
        ; width; height }
    | [] -> empty

let sub_cols start len {elems; width; height} =
    let len = Option.value len ~default: (width - start) in
    let stop = start + len in
    if 0 <= start && start <= width
        && 0 <= stop && stop <= width
    then { elems =
            (let open Stream.Syntax in
            let* rowi = Stream.range 0 height in
            let* coli = Stream.range start stop in
            yield (Vector.get elems (rowi * width + coli)))
            |> Stream.into (Sink.buffer (height * len))
            |> Vector.of_array_unsafe
        ; width = len; height }
    else raise (Invalid_argument "sub_cols: out of bounds")

let remove_col coli {elems; width; height} =
    { elems =
        (let open Stream.Syntax in
        let* rowi = Stream.range 0 height in
        let* coli = Stream.range 0 width in
        yield (coli, rowi * width + coli))
        |> Stream.filter (fun (coli', _) -> coli' <> coli)
        |> Stream.map (fun (_, i) -> Vector.get elems i)
        |> Stream.into (Sink.buffer (height * (width - 1)))
        |> Vector.of_array_unsafe
    ; width = width - 1; height }

let select_rows rowis ({elems; width; height = _} as mat) = 
    let height = IntSet.cardinal rowis in
    { elems = Stream.from (Source.seq (IntSet.to_seq rowis))
        |> Stream.flat_map (fun rowi -> match row rowi mat with
            | Some row -> Stream.from row
            | None -> raise (Invalid_argument "select_rows: out of bounds index"))
        |> Stream.into (Sink.buffer (width * height))
        |> Vector.of_array_unsafe
    ; height; width }

