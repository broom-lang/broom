type log
type 'a rref

val log : unit -> log
val transaction : log -> (unit -> 'a) -> 'a

val ref : 'a -> 'a rref
val (!) : 'a rref -> 'a
val set : log -> 'a rref -> 'a -> unit
val eq : 'a rref -> 'a rref -> bool

module Store : UnionFind.STORE
    with type 'a store = log
    with type 'a rref = 'a rref

