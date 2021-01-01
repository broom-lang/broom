type 'a t = 'a -> PPrint.document

let of_grammar g =
    let open PPrint in
    let (let*) = Option.bind in
    let rec of' : type a . a Grammar.t -> (a -> PPrint.document option) = function
        | Grammar.Map (f, g) ->
            let p = of' g in
            (fun x -> Option.bind (PIso.unapply f x) p)
        | AndThen (g, g') ->
            let p = of' g in
            let p' = of' g' in
            (fun (x, y) ->
                let* xd = p x in
                let* yd = p' y in
                Some (xd ^^ yd))
        | Pure x -> (fun y ->
            if y = x (* HACK *)
            then Some empty
            else None)
        | Either (g, g') ->
            let p = of' g in
            let p' = of' g' in
            (fun x -> match p x with
                | Some _ as res -> res
                | None -> p' x)
        | Fail -> Fun.const None
        | Fix f -> (fun x -> of' (f (Grammar.fix f)) x) (* OPTIMIZE *)
        | Token -> (fun c -> Some (char c)) in
    let p = of' g in
    fun x -> p x |> Option.get

