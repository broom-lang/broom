type t =
    | IAdd | ISub | IMul

val of_string : string -> t option
val to_doc : t -> PPrint.document

