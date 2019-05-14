structure Either :> sig
    datatype ('l, 'r) t = Left of 'l
                        | Right of 'r

    val unwrap: ('l, 'r) t -> 'r
    val map: ('r -> 'r') -> ('l, 'r) t -> ('l, 'r') t
end = struct
    datatype ('l, 'r) t = Left of 'l
                        | Right of 'r

    val unwrap = fn Left _ => raise Domain
                  | Right v => v

    fun map f =
        fn Left l => Left l
         | Right r => Right (f r)
end
