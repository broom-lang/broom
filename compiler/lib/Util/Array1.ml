include Array

let of_array xs = if length xs > 0 then Some xs else None

let to_array = Fun.id

let to_source xs =
    let len = length xs in
    Streaming.Source.unfold 0 (fun i ->
        if i < len
        then Some (get xs i, i + 1)
        else None
    )

