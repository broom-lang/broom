structure Either :> sig
    datatype ('l, 'r) t = Left of 'l
                        | Right of 'r
end = struct
    datatype ('l, 'r) t = Left of 'l
                        | Right of 'r
end
