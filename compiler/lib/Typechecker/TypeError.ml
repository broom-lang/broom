type t' =
    | Unbound of Name.t

type t = t' Util.with_pos

let to_doc (err : t) = Asserts.todo (Some err.pos)

