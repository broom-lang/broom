module T = FcType.Type

type t =
    | IAdd | ISub | IMul
    | Int
    | Type

val of_string : string -> t option
val to_doc : t -> PPrint.document

