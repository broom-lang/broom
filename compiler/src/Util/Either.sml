structure Either :> sig
    datatype ('l, 'r) t = Left of 'l
                        | Right of 'r

    val map: ('r -> 'r') -> ('l, 'r) t -> ('l, 'r') t
end = struct
    datatype ('l, 'r) t = Left of 'l
                        | Right of 'r

    fun map f =
        fn Left l => Left l
         | Right r => Right (f r)
end
