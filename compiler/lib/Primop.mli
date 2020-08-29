module T = FcType.Type

type t =
    | IAdd | ISub | IMul
    | Int
    | Type

val of_string : string -> t option
val to_doc : t -> PPrint.document

val typeof : t -> T.kind Vector.t * (T.locator * T.t) Vector.t * T.t * T.abs

