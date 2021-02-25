type t =
    | IAdd | ISub | IMul | IDiv
    | ILt | ILe | IGt | IGe | IEq

val of_string : string -> t option
val to_doc : t -> PPrint.document

