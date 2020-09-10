include CCImmutArray

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

let build vec = of_array_unsafe (CCVector.to_array vec)

