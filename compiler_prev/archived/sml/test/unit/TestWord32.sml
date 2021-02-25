structure TestWord32 = struct
    open Word32
    infix 5 >>

    structure Assert = Assert(struct
        type t = word

        val eq = op=
        val toString = Word32.toString
    end)
    open Assert

    fun testBitCount () =
        let fun subBit (n, i) = andb (n >> i, 0w1)
         
            fun slowBitCount n =
                let fun loop i acc =
                        if i < 0w32
                        then loop (i + 0w1)
                                  (acc + subBit (n, i))
                        else acc
                in loop 0w0 0w0
                end

            fun testRange (start, endd, step) =
                let fun loop i =
                        if (Int.> (step, 0) andalso i < endd)
                           orelse i > endd
                        then ( Assert.eq (bitCount i, slowBitCount i) (toString i)
                             ; loop (if Int.> (step, 0)
                                     then i + fromInt step
                                     else i - fromInt (Int.~ step)) )
                        else ()
                in loop start
                end
        in testRange (0w0, 0w300, 10)
         ; testRange (0w0, 0w0 - 0w1000000000, 100000000)
         ; testRange (0w0, 0w0 - 0w300, ~10)
        end

    fun runTests () =
        testBitCount ()
end

