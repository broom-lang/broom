structure Vector = struct
    open Vector

    val fromArray = Array.vector

    fun toArray vs = Array.tabulate (length vs, fn i => sub (vs, i))

    fun uncons xs =
        if length xs > 0
        then SOME (sub (xs, 0), VectorSlice.slice (xs, 1, NONE))
        else NONE

    fun prepend (x, ys) =
        let val len = Vector.length ys + 1
            val {update, done, ...} = MLton.Vector.create len
        in update (0, x)
         ; Vector.appi (fn (i, y) => update (i + 1, y)) ys
         ; done ()
        end

    fun append (xs, y) =
        let val len = Vector.length xs + 1
            val {update, done, ...} = MLton.Vector.create len
        in Vector.appi update xs
         ; update (len - 1, y)
         ; done ()
        end

    fun pushAt (xs, i, y) =
        let val len = Vector.length xs + 1
            val {update, done, ...} = MLton.Vector.create len
            val _ = VectorSlice.appi update (VectorSlice.slice (xs, 0, SOME i))
            val _ = update (i, y)
            fun loop j =
                if j < len
                then ( update (j, Vector.sub (xs, j - 1))
                     ; loop (j + 1) )
                else done ()
        in loop (i + 1)
        end

    fun splitWith pred xs =
        let fun loop i =
                if i < Vector.length xs andalso pred (Vector.sub (xs, i))
                then loop (i + 1)
                else (VectorSlice.slice (xs, 0, SOME i), VectorSlice.slice (xs, i, NONE))
        in loop 0
        end

    (* OPTIMIZE: *)
    fun flatMap f xs =
        foldl (fn (x, acc) => concat [acc, f x]) #[] xs

    fun zipWith f (xs, ys) =
        let val len = Int.min (Vector.length xs, Vector.length ys)
            val {update, done, ...} = MLton.Vector.create len
            fun loop i =
                if i < len
                then ( update (i, f (Vector.sub (xs, i), Vector.sub (ys, i)))
                     ; loop (i + 1) )
                else ()
        in loop 0
         ; done ()
        end

    fun zip vecs = zipWith Fn.identity vecs

    fun zip3With f (xs, ys, zs) =
        let val len = Int.min (Int.min (Vector.length xs, Vector.length ys), Vector.length zs)
            val {update, done, ...} = MLton.Vector.create len
            fun loop i =
                if i < len
                then ( update (i, f (Vector.sub (xs, i), Vector.sub (ys, i), Vector.sub (zs, i)))
                     ; loop (i + 1) )
                else ()
        in loop 0
         ; done ()
        end

    fun stableSort cmp vs =
        let val arr = toArray vs
        in Array.stableSort cmp arr
         ; fromArray arr
        end

    fun inspect inspectEl vs =
        "#" ^ Int.toString (length vs) ^ "["
        ^ foldl (fn (v, res) => res ^ ", " ^ inspectEl v) "" vs ^ "]"
end
