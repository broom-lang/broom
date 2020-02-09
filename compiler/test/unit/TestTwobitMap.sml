structure TestTwobitMap = struct
    structure Assert = Assert(struct
        type t = Word8Vector.vector

        fun eq (xs, ys) =
            Word8Vector.length xs = Word8Vector.length ys
            andalso Word8Vector.collate Word8.compare (xs, ys) = EQUAL

        fun toString vs =
            if Word8Vector.length vs = 0
            then "[]"
            else "[" ^ Word8VectorSlice.foldl (fn (v, acc) => acc ^ ", " ^ Word8.fmt StringCvt.DEC v)
                                              (Word8.fmt StringCvt.DEC (Word8Vector.sub (vs, 0)))
                                              (Word8VectorSlice.slice (vs, 1, NONE))
                 ^ "]"
    end)
    open Assert

    fun testRoundtrip () =
        let fun loop len =
                if len < 8
                then let val vs = Word8Vector.tabulate (len, fn i => Word8.fromInt ((i mod 2) + 1))
                     in Assert.eq (vs, TwobitMap.unpack (TwobitMap.pack vs)) (Int.toString len)
                      ; loop (len + 1)
                     end
                else ()
        in loop 0
        end

    fun runTests () =
        testRoundtrip ()
end

