open Streaming

type t =
    | Ov of {name : Name.t; kind : kind}
    | Bv of {depth : int; sibli : int; kind : kind}
    | Exists of {existentials : kind Vector1.t; body : t}
    | Pi of {universals : kind Vector.t; domain : t; codomain : t}
    | Fn of {param : kind; body : t}
    | App of {callee : t; arg : t}
    | Record of t
    | With of {base : t; label : Name.t; field : t}
    | EmptyRow
    | Tuple of t Vector.t
    | Proxy of t
    | PromotedTuple of t Vector.t
    | PromotedArray of t Vector.t
    | Prim of Prim.t

and kind = t

(* --- *)

let exists_prec = 0
let pi_prec = exists_prec
let fn_prec = pi_prec
let with_prec = fn_prec + 1
let app_prec = with_prec + 1

let prec_parens required doc = if required then PPrint.parens doc else doc

let rec to_doc t =
    let open PPrint in

    let rec to_doc_prec prec = function
        | Exists {existentials; body} ->
            prefix 4 1
                (string "exists" ^/^ tparams_to_doc (Vector1.to_list existentials))
                (dot ^^ blank 1 ^^ to_doc_prec exists_prec body)
            |> prec_parens (prec > exists_prec)

        | Pi {universals; domain; codomain} when Vector.length universals > 0 ->
            prefix 4 1
                (string "forall" ^/^ tparams_to_doc (Vector.to_list universals))
                (dot ^^ blank 1
                ^^ infix 4 1 (string "->")
                    (to_doc_prec (pi_prec + 1) domain) (to_doc_prec pi_prec codomain))
            |> prec_parens (prec > pi_prec)

        | Pi {universals = _; domain; codomain} ->
            infix 4 1 (string "->")
                (to_doc_prec (pi_prec + 1) domain) (to_doc_prec pi_prec codomain)

        | Fn {param; body} ->
            prefix 4 1
                (string "fn" ^/^ to_doc param)
                (dot ^^ blank 1 ^^ to_doc_prec fn_prec body)
            |> prec_parens (prec > fn_prec)

        | App {callee; arg} ->
            prefix 4 1 (to_doc_prec app_prec callee) (to_doc_prec (app_prec + 1) arg)
            |> prec_parens (prec > app_prec)

        | Record row -> braces (to_doc row)

        | With {base; label; field} ->
            infix 4 1 (string "with" ^^ blank 1 ^^ Name.to_doc label ^^ blank 1 ^^ equals)
                (to_doc_prec with_prec base) (to_doc_prec (with_prec + 1) field)
            |> prec_parens (prec > with_prec)

        | EmptyRow -> parens bar

        | Proxy carrie -> brackets (prefix 4 1 equals (to_doc carrie))

        | Tuple typs ->
            surround_separate_map 4 1 (parens colon)
                (lparen ^^ colon) (comma ^^ break 1) rparen
                to_doc (Vector.to_list typs)

        | PromotedTuple typs ->
            surround_separate_map 4 1 (parens empty)
                lparen (comma ^^ break 1) rparen
                to_doc (Vector.to_list typs)

        | PromotedArray typs ->
            surround_separate_map 4 1 (brackets empty)
                lbracket (comma ^^ break 1) rbracket
                to_doc (Vector.to_list typs)

        | Ov {name; kind = _} -> Name.to_doc name

        | Bv {depth; sibli; kind = _} ->
            string (Int.to_string depth) ^^ dot ^^ string (Int.to_string sibli)

        | Prim pt -> string "__" ^^ Prim.to_doc pt in

    to_doc_prec 0 t

and kind_to_doc t = to_doc t

and tparams_to_doc kinds = PPrint.(separate_map (break 1) kind_to_doc kinds)

(* --- *)

let map_children =
        let all_eq xs ys =
            Stream.from (Source.zip_with (==) (Vector.to_source xs) (Vector.to_source ys))
            |> Stream.into (Sink.all ~where: Fun.id) in

        fun f t ->
            match t with
            | Fn {param; body} ->
                let body' = f body in
                if body' == body then t else Fn {param; body = body'}

            | App {callee; arg} ->
                let callee' = f callee in
                let arg' = f arg in
                if callee' == callee && arg' == arg
                then t
                else App {callee = callee'; arg = arg'}

            | Exists {existentials; body} ->
                let body' = f body in
                if body' == body then t else Exists {existentials; body = body'}

            | Pi {universals; domain; codomain} ->
                let domain' = f domain in
                let codomain' = f codomain in
                if domain' == domain && codomain' == codomain
                then t
                else Pi {universals; domain = domain'; codomain = codomain'}

            | Record row ->
                let row' = f row in
                if row' == row then t else Record row'

            | With {base; label; field} ->
                let base' = f base in
                let field' = f field in
                if base' == base && field' == field
                then t
                else With {base = base'; label; field = field'}

            | Proxy carrie ->
                let carrie' = f carrie in
                if carrie' == carrie then t else Proxy carrie'

            | Tuple typs ->
                let typs' = Vector.map f typs in
                if all_eq typs' typs then t else Tuple typs

            | PromotedTuple typs ->
                let typs' = Vector.map f typs in
                if all_eq typs' typs then t else PromotedTuple typs

            | PromotedArray typs ->
                let typs' = Vector.map f typs in
                if all_eq typs' typs then t else PromotedArray typs

            | EmptyRow | Prim _ | Bv _ | Ov _ -> t

(* --- *)

let expose =
    let rec expose subst depth t = match t with
        | Bv {depth = depth'; sibli; kind = _} as typ ->
            if depth' = depth
            then Vector.get subst sibli
            else typ

        | Exists {existentials; body} ->
            let body' = expose subst (depth + 1) body in
            if body' == body then t else Exists {existentials; body = body'}

        | Pi {universals; domain; codomain} ->
            let depth = depth + 1 in
            let domain' = expose subst depth domain in
            let codomain' = expose subst depth codomain in
            if domain' == domain && codomain' == codomain
            then t
            else Pi {universals; domain = domain'; codomain = codomain'}

        | Fn {param; body} ->
            let body' = expose subst (depth + 1) body in
            if body' == body then t else Fn {param; body = body'}

        | App _ | Record _ | With _ | EmptyRow | Tuple _
        | Proxy _ | PromotedTuple _ | PromotedArray _
        | Ov _ | Prim _ -> map_children (expose subst depth) t in

    fun subst t -> expose subst 0 t

let close =
    let rec close subst depth t = match t with
        | Ov {name; kind} ->
            (match Name.HashMap.get name subst with
            | Some sibli -> Bv {depth; sibli; kind}
            | None -> t)

        | Exists {existentials; body} ->
            let body' = close subst (depth + 1) body in
            if body' == body then t else Exists {existentials; body = body'}

        | Pi {universals; domain; codomain} ->
            let depth = depth + 1 in
            let domain' = close subst depth domain in
            let codomain' = close subst depth codomain in
            if domain' == domain && codomain' == codomain
            then t
            else Pi {universals; domain = domain'; codomain = codomain'}

        | Fn {param; body} ->
            let body' = close subst (depth + 1) body in
            if body' == body then t else Fn {param; body = body'}

        | App _ | Record _ | With _ | EmptyRow | Tuple _
        | Proxy _ | PromotedTuple _ | PromotedArray _
        | Bv _ | Prim _ -> map_children (close subst depth) t in

    fun subst t -> close subst 0 t

