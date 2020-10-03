include CCImmutArray

open Streaming

let fold_right f acc xs =
    let rec loop acc i =
        if i >= 0
        then loop (f acc (get xs i)) (i - 1)
        else acc in
    loop acc (length xs - 1)

let iter2 f xs ys =
    if length ys = length xs
    then iteri (fun i x -> f x (get ys i)) xs
    else raise (Invalid_argument "Vector.iter2: inequal lengths")

let map2 f xs ys =
    if length ys = length xs
    then mapi (fun i x -> f x (get ys i)) xs
    else raise (Invalid_argument "Vector.map2: inequal lengths")

let map3 f xs ys zs =
    let len = length xs in
    if length ys = len && length zs = len
    then mapi (fun i x -> f x (get ys i) (get zs i)) xs
    else raise (Invalid_argument "Vector.map3: inequal lengths")

let fold2 f acc xs ys =
    if length ys = length xs
    then foldi (fun acc i x -> f acc x (get ys i)) acc xs
    else raise (Invalid_argument "Vector.fold_left2: inequal lengths")

let to_seq xs =
    let len = length xs in
    Seq.unfold (fun i ->
        if i < len
        then Some (get xs i, i + 1)
        else None
    ) 0

let of_seq seq = of_array_unsafe (Array.of_seq seq)

let to_source xs =
    let len = length xs in
    Streaming.Source.unfold 0 (fun i ->
        if i < len
        then Some (get xs i, i + 1)
        else None
    )

let build vec = of_array_unsafe (CCVector.to_array vec)

let sink () = Sink.make
    ~init: CCVector.create
    ~push: (fun xs x -> CCVector.push xs x; xs)
    ~stop: build ()

let concat vecs = Stream.from (Source.list vecs)
    |> Stream.flat_map (fun xs -> Stream.from (xs |> to_source))
    |> Stream.into (sink ())

let remove xs i =
    let len = length xs in
    if i >= 0 && i < len
    then Stream.concat
            (Stream.take i (Stream.from (to_source xs)))
            (Stream.drop (i + 1) (Stream.from (to_source xs)))
        |> Stream.into (Sink.buffer (len - 1))
        |> of_array_unsafe
    else raise (Invalid_argument "Vector.remove: index out of bounds")

let select xs is =
    Stream.from (Source.seq (IntSet.to_seq is))
    |> Stream.map (get xs)
    |> Stream.into (Sink.buffer (IntSet.cardinal is))
    |> of_array_unsafe

