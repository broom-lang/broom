module type TRANSACTABLE = sig
    type log
    type contents
    type ref

    val ref : contents -> ref
    val get : ref -> contents
    val set : log -> ref -> contents -> unit
end

module type S = sig
    type log

    val log : unit -> log
    val transaction : log -> (unit -> 'a) -> 'a

    module Type : TRANSACTABLE
    module Expr : TRANSACTABLE
    module Uv : TRANSACTABLE
end

module type TRANSACTABLES = sig
    type typ
    type expr
    type uvv
end

module Make (Transactables : TRANSACTABLES) : S
    with type Type.contents = Transactables.typ
    with type Expr.contents = Transactables.expr
    with type Uv.contents = Transactables.uvv

