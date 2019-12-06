structure TestHashMap = struct
    structure Map = HashMap(struct
        type hash_key = int
        val hashVal = Word32.fromInt
        val sameKey = op=
        val toString = Int.toString
    end)

    structure Assert = Assert(struct
        type t = int

        val eq = op=
        val toString = Int.toString
    end)
    open Assert

    fun testEmpty () =
        let val kvs = Map.empty
        in Assert.eq (Map.length kvs, 0) "zero size"
         ; Assert.ok (Map.find kvs 0 = NONE) "0 not found"
         ; Assert.ok (Map.find kvs 1 = NONE) "1 not found"
        end

    fun testInsert () =
        let val vs = Vector.tabulate (100, fn n => 99 - n)
            
            val kvs = Vector.foldli (fn (k, v, acc) => Map.insert acc (k, v))
                                    Map.empty vs
        in Assert.eq (Map.length kvs, 100) "100 items"
         ; Vector.appi (fn (k, v) =>
                            case Map.find kvs k
                            of SOME v' => Assert.eq (v', v) (Int.toString k)
                             | NONE => Assert.ok false (Int.toString k ^ " found"))
                       vs
         ; Assert.ok (Map.find kvs 101 = NONE) "101 not found"
        end

    fun runTests () =
        ( testEmpty ()
        ; testInsert () )
end

