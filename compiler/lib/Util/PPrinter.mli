type 'a t = 'a -> PPrint.document

val of_grammar : 'a Grammar.t -> 'a t

