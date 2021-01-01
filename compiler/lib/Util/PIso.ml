type ('a, 'b) t = {apply : 'a -> 'b option; unapply : 'b -> 'a option}

let apply {apply; _} = apply
let unapply {unapply; _} = unapply

let piso apply unapply = {apply; unapply}

let inv {apply; unapply} = {apply = unapply; unapply = apply}

let comp piso' piso =
    { apply = (fun x -> Option.bind (apply piso x) (apply piso'))
    ; unapply = (fun x -> Option.bind (unapply piso' x) (unapply piso)) }

let id = {apply = Option.some; unapply = Option.some}

let unit = {apply = (fun x -> Some (x, ())); unapply = (fun (x, ()) -> Some x)}

let element x = piso
    (fun () -> Some x)
    (fun x' -> if x' = x (* HACK *) then Some () else None)

let subset pred =
    let f x = if pred x then Some x else None in
    piso f f

let some = {apply = (fun x -> Some (Some x)); unapply = Fun.id}
let none = {apply = (fun () -> None); unapply = (function
    | None -> Some ()
    | Some _ -> None)}

let cons = { apply = (fun (x, xs) -> Some (x :: xs)); unapply = (function
    | x :: xs -> Some (x, xs)
    | [] -> None)}
let nil = { apply = (fun () -> Some []); unapply = (function
    | [] -> Some ()
    | _ :: _ -> None)}

