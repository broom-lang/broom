module T = FcType.Type

type t =
    | IAdd | ISub | IMul | IDiv
    | ILt | ILe | IGt | IGe | IEq
    | CellNew | CellInit | CellGet
    | Int
    | Type

val of_string : string -> t option
val to_doc : t -> PPrint.document

