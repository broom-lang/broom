structure Word32 = struct
    open Word32
    infix 5 << >>

    local
        val c1 : word = 0wx55555555 (* 0101... *)
        val c2 : word = 0wx33333333 (* 0011... *)
        val c4 : word = 0wx0f0f0f0f (* 00001111... *)
        val c01 : word = 0wx01010101 (* 00000001... *)
    in
        (* Seems we can't access the popcount instruction but this 'Wilkes-Wheeler-Gill'
           function should not be too bad: *)
        fun bitCount x =
            let val x = x - andb (x >> 0w1, c1)
                val x = andb (x, c2) + andb(x >> 0w2, c2)
                val x = andb (x + (x >> 0w4), c4)
            in (x * c01) >> 0w24
            end
    end
end

