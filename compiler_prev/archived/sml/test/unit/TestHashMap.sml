structure TestHashMap = struct
    structure Map = HashMapFn(struct
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
        let val vs = Vector.tabulate (1000, fn n => 999 - n)
            
            val kvs = Vector.foldli (fn (k, v, acc) => Map.insert acc (k, v))
                                    Map.empty vs
            val kvs' = Map.insert kvs (23, 42)
        in Assert.eq (Map.length kvs, 1000) "1000 items"
         ; Vector.appi (fn (k, v) =>
                            case Map.find kvs k
                            of SOME v' => Assert.eq (v', v) (Int.toString k)
                             | NONE => Assert.ok false (Int.toString k ^ " found"))
                       vs
         ; Assert.ok (Map.find kvs 1001 = NONE) "1001 not found"
         ; Assert.eq (valOf (Map.find kvs 23), 999 - 23) "kvs 23 unchanged"
         ; Assert.eq (valOf (Map.find kvs' 23), 42) "kvs' 23 updated"
        end

    fun runTests () =
        ( testEmpty ()
        ; testInsert () )
end

