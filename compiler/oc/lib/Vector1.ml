type 'a t = 'a Vector.t

let singleton = Vector.singleton

let get = Vector.get

let of_vector vec =
    if Vector.length vec > 0
    then Some vec
    else None

let to_vector = Fun.id

let of_list = function
    | (_ :: _) as ls -> Some (Vector.of_list ls)
    | [] -> None

let to_list = Vector.to_list

let append = Vector.append

let fold_left = Vector.fold_left
let for_all = Vector.for_all
let exists = Vector.exists
let map = Vector.map
let mapi = Vector.mapi
let map2 = Vector.map2
let iter = Vector.iter

let fold_left2 = Vector.fold_left2

