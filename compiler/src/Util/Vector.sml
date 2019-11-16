structure Vector = struct
    open Vector

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

    fun inspect inspectEl vs =
        "#" ^ Int.toString (length vs) ^ "["
        ^ foldl (fn (v, res) => res ^ ", " ^ inspectEl v) "" vs ^ "]"
end
