type 'a t = 'a Array.t

let empty () = Array.of_list []
let singleton v = Array.make 1 v

let length = Array.length
let get = Array.get

let init = Array.init
let of_list = Array.of_list
let to_list = Array.to_list
let of_seq = Array.of_seq
let to_seq = Array.to_seq

let fold_left = Array.fold_left
let fold_right = Array.fold_right
let for_all = Array.for_all
let exists = Array.exists
let iter2 = Array.iter2
let map = Array.map
let mapi = Array.mapi
let map2 = Array.map2
let iter = Array.iter

let map3 f xs ys zs =
    let len = length xs in
    if length ys = len && length zs = len
    then mapi (fun i x -> f x (get ys i) (get zs i)) xs
    else raise (Invalid_argument "Vector.map3: inequal lengths")

let find_opt pred xs =
    let len = length xs in
    let rec loop i =
        if i < len
        then
            let x = get xs i in
            if pred x
            then Some x
            else loop (i + 1)
        else None in
    loop 0

let find pred xs = match find_opt pred xs with
    | Some x -> x
    | None -> raise Not_found

let split vec =
    ( Array.init (length vec) (fun i -> fst (get vec i))
    , Array.init (length vec) (fun i -> snd (get vec i)) )

let sub = Array.sub
let append = Array.append

let fold_left2 f acc xs ys =
    let len = length xs in
    if length ys = length xs
    then
        let rec fold acc i =
            if i < len
            then fold (f acc (get xs i) (get ys i)) (i + 1)
            else acc in
        fold acc 0
    else raise (Invalid_argument "Vector.fold_left2: inequal lengths")

