structure TestTrictor = struct
    structure Assert = Assert(struct
        type t = int

        val eq = op=
        val toString = Int.toString
    end)
    open Assert

    fun testEmpty () =
        let val v = Trictor.empty ()
        in Assert.eq (Trictor.length v, 0) "empty"
         ; ( Trictor.sub (v, 0)
           ; Assert.ok false "should raise Subscript" )
           handle Subscript => ()
        end

    fun testAppend () =
        let val xs = Vector.tabulate (100, fn n => 99 - n)
            val ys = Vector.foldl (fn (x, ys) => Trictor.append ys x)
                                  (Trictor.empty ()) xs
            fun loop i =
                if i < Vector.length xs
                then Assert.eq (Trictor.sub (ys, i), Vector.sub (xs, i))
                               ("at index " ^ Int.toString i)
                else ()
        in Assert.eq (Trictor.length ys, Vector.length xs) "lengths"
         ; loop 0
        end

    fun testUpdate () =
        let val xs = Trictor.fromVector (Vector.tabulate (100, fn n => 99 - n))
            val xs' = Trictor.update (xs, 23, 42)
        in Assert.eq (Trictor.sub (xs', 23), 42) "xs' updated"
         ; Assert.eq (Trictor.sub (xs, 23), 99 - 23) "xs did not update"
        end

    fun testGet () =
        let val xs = Trictor.fromVector (Vector.tabulate (10, fn n => 9 - n))
            val ys = Trictor.fromVector (Vector.tabulate (100, fn n => 99 - n))
        in Assert.eq (Trictor.sub (xs, 7), 9 - 7) "xs[7]"
         ; Assert.eq (Trictor.sub (ys, 7), 99 - 7) "ys[7]"
         ; Assert.eq (Trictor.sub (ys, 95), 99 - 95) "ys[95]"
         ; Assert.eq (Trictor.sub (ys, 96), 99 - 96) "ys[96]"
         ; Assert.eq (Trictor.sub (ys, 99), 0) "ys[99]"
        end

    fun testFoldl () =
        let val xs = Vector.tabulate (100, fn n => 99 - n)
            val ys = Vector.foldl (fn (x, ys) => Trictor.append ys x)
                                  (Trictor.empty ()) xs
        in Assert.eq (Trictor.foldl op+ 0 ys, Vector.foldl op+ 0 xs) "sums"
        end
        
    fun runTests () =
        ( testEmpty ()
        ; testAppend ()
        ; testUpdate ()
        ; testGet ()
        ; testFoldl () )
end

val status =
    ( TestTrictor.runTests ()
    ; OS.Process.success )
    handle TestTrictor.Assert.AssertFailed msg =>
            ( TextIO.output (TextIO.stdErr, "Assert failed: " ^ msg ^ "\n")
            ; OS.Process.failure )

do OS.Process.exit status

