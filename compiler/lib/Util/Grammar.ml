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

    | Printer : ('a -> PPrint.document option) -> 'a t
    | Group : 'a t -> 'a t
    | Nest : int * 'a t -> 'a t

let map f g = Map (f, g)
let and_then g g' = AndThen (g, g')
let pure x = Pure x

let either g g' = Either (g, g')
let fail = Fail

let fix f = Fix f
let printer p = Printer p

let char = Token

let group g = Group g
let blank n = let doc = Some (PPrint.blank n) in printer (fun () -> doc)
let break n = let doc = Some (PPrint.break n) in printer (fun () -> doc)
let nest n g = Nest (n, g)

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

let prefix n b op x = group (op <*> nest n (break b *> x))

let infix n b op l r = prefix n b (l <* blank b <* op) r

let separate1 sep g = cons <$> (g <*> many (sep *> g))

let between l r g = l *> g <* r

let surround n b l g r =
    group (between l r (nest n (break b *> g)) <* break b)

let surround_separate n b void l sep r g =
    surround n b l (vector <$> separate1 sep g) r
    <|> void

let sat pred = subset pred <$> char

let token c = inv (element c) <$> sat ((=) c)

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

let lparen = token '('
let rparen = token ')'
let parens g = between lparen rparen g
let lbracket = token '['
let rbracket = token ']'
let brackets g = between lbracket rbracket g
let lbrace = token '{'
let rbrace = token '}'
let braces g = between lbrace rbrace g

let dot = token '.'
let comma = token ','
let colon = token ':'

let equals = token '='
let bar = token '|'
let caret = token '^'
let slash = token '/'

