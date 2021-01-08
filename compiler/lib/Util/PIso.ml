type ('a, 'b) t = {apply : 'a -> 'b option; unapply : 'b -> 'a option}

let apply {apply; _} = apply
let unapply {unapply; _} = unapply

let piso apply unapply = {apply; unapply}
let iso apply unapply = piso (fun x -> Some (apply x)) (fun x -> Some (unapply x))
let prism apply unapply = piso (fun x -> Some (apply x)) unapply

let inv {apply; unapply} = {apply = unapply; unapply = apply}

let comp piso' piso =
    { apply = (fun x -> Option.bind (apply piso x) (apply piso'))
    ; unapply = (fun x -> Option.bind (unapply piso' x) (unapply piso)) }

let id = {apply = Option.some; unapply = Option.some}

let unit = {apply = (fun x -> Some (x, ())); unapply = (fun (x, ()) -> Some x)}

let element x = piso
    (fun () -> Some x)
    (fun x' -> if x' = x (* HACK *) then Some () else None)

let map_snd {apply; unapply} = piso
    (fun (l, r) -> apply r |> Option.map (fun r -> (l, r)))
    (fun (l, r) -> unapply r |> Option.map (fun r -> (l, r)))

let subset pred =
    let f x = if pred x then Some x else None in
    piso f f

let fold_left {apply; unapply} =
    let rec fold acc = function
        | x :: xs -> Option.bind (apply (acc, x)) (fun acc -> fold acc xs)
        | [] -> Some acc in
    let rec unfold xs s = match unapply s with
        | Some (s, x) -> unfold (x :: xs) s
        | None -> Some (s, xs) in
    { apply = (fun (init, xs) -> fold init xs)
    ; unapply = (unfold []) }

let some = {apply = (fun x -> Some (Some x)); unapply = Fun.id}
let none = {apply = (fun () -> None); unapply = (function
    | None -> Some ()
    | Some _ -> None)}

let cons = {apply = (fun (x, xs) -> Some (x :: xs)); unapply = (function
    | x :: xs -> Some (x, xs)
    | [] -> None)}
let nil = {apply = (fun () -> Some []); unapply = (function
    | [] -> Some ()
    | _ :: _ -> None)}

let opt_non_empty_list =
    { apply = (function Some xs -> Some xs | None -> Some [])
    ; unapply = (function [] -> Some None | xs -> Some (Some xs)) }

let vector = {apply = (fun xs -> Some (Vector.of_list xs)); unapply = (fun xs ->
    Some (Vector.to_list xs))}

let string = iso
    (fun cs -> cs |> List.to_seq |> String.of_seq)
    (fun s -> s |> String.to_seq |> List.of_seq)

