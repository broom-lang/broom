open Streaming
open PIso

type _ t =
    | Map : ('a, 'b) PIso.t * 'a t -> 'b t
    | AndThen : 'a t * 'b t -> ('a * 'b) t
    | Pure : 'a -> 'a t
    | Either : 'a t * 'a t -> 'a t
    | Fail : 'a t
    | Fix : ('a t -> 'a t) -> 'a t
    | Token : char t

let map f g = Map (f, g)
let and_then g g' = AndThen (g, g')
let pure x = Pure x

let either g g' = Either (g, g')
let fail = Fail

let char = Token

let fix f = Fix f

module Infix = struct
    let (<$>) = map
    let (<*>) = and_then
    let (<*) g g' =
        let f = PIso.piso (fun (x, ()) -> Some x) (fun x -> Some (x, ())) in
        f <$> (g <*> g')
    let ( *>) g g' =
        let f = PIso.piso (fun ((), x) -> Some x) (fun x -> Some ((), x)) in
        f <$> (g <*> g')
    let (<|>) = either
end

open Infix

let opt g = some <$> g <|> pure None

let many g = fix (fun self -> cons <$> (g <*> self) <|> pure [])

let many1 g = cons <$> (g <*> many g)

let token c = inv (element c) <$> (subset ((=) c) <$> char)

let text s =
     Stream.from (Source.string s)
        |> Stream.map token
        |> Stream.into (Sink.fold ( *>) (pure ()))

let digit =
    let pred c = 
        let n = Char.code c in
        48 <= n && n < 58 in
    subset pred <$> char

let int =
    let f = piso
        (fun (sign, dcs) ->
            let n = dcs |> List.to_seq |> String.of_seq |> int_of_string in
            Some (if Option.is_some sign then -n else n))
        (fun n ->
            let sign = if n >= 0 then None else Some () in
            let cs = abs n |> Int.to_string |> String.to_seq |> List.of_seq in
            Some (sign, cs)) in
    f <$> (opt (token '-') <*> many1 digit)

