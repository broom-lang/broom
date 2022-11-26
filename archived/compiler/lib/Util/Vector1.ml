type 'a t = 'a Vector.t

let singleton = Vector.singleton

let length = Vector.length
let get = Vector.get

let of_vector vec =
    if Vector.length vec > 0
    then Some vec
    else None

let to_vector = Fun.id

let to_array = Vector.to_array

let of_list = function
    | (_ :: _) as ls -> Some (Vector.of_list ls)
    | [] -> None

let to_list = Vector.to_list

let append = Vector.append

let fold = Vector.fold
let foldi = Vector.foldi
let exists = Vector.exists
let map = Vector.map
let map_children = Vector.map_children
let mapi = Vector.mapi
let map2 = Vector.map2
let iter = Vector.iter
let iter2 = Vector.iter2

let fold2 = Vector.fold2

let to_source = Vector.to_source

let sink () = Streaming.Sink.map of_vector (Vector.sink ())

