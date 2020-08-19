type t = Int | Bool | EmptyRow

val to_doc : t -> PPrint.document

val eq : t -> t -> bool

