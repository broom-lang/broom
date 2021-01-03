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
        | Fix f ->
            let rec p = lazy (of' (f (Grammar.printer (fun x -> Lazy.force p x)))) in
            Lazy.force p
        | Token -> (fun c -> Some (char c))

        | Printer p -> p
        | Group g ->
            let p = of' g in
            (fun x -> p x |> Option.map group)
        | Nest (n, g) ->
            let p = of' g in
            (fun x -> p x |> Option.map (nest n)) in
    let p = of' g in
    fun x -> p x |> Option.get

