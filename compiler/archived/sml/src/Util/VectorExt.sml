structure VectorExt = struct
    open Vector

    val fromArray = Array.vector

    fun toArray vs = Array.tabulate (length vs, fn i => sub (vs, i))

    fun toList vs = List.tabulate (length vs, fn i => sub (vs, i))

    fun uncons xs =
        if length xs > 0
        then SOME (sub (xs, 0), VectorSlice.slice (xs, 1, NONE))
        else NONE

    fun prepend (x, ys) =
        let val len = Vector.length ys + 1
        in tabulate (len, fn i =>
                              if i = 0
                              then x
                              else sub (ys, i - 1))
        end

    fun append (xs, y) =
        let val len = Vector.length xs + 1
        in tabulate (len, fn i =>
                              if i < len - 1
                              then sub (xs, i)
                              else y)
        end

    fun pushAt (xs, i, y) =
        let val len = Vector.length xs + 1
        in tabulate (len, fn j =>
                              case Int.compare (j, i)
                              of LESS => sub (xs, j)
                               | EQUAL => y
                               | GREATER => sub (xs, j - 1))
        end

    fun rev xs =
        let val len = length xs
            val lastIndex = len - 1
        in tabulate (len, fn i => sub (xs, lastIndex - i))
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
        let val len = Int.min (length xs, length ys)
        in tabulate (len, fn i => f (sub (xs, i), sub (ys, i)))
        end

    fun zip vecs = zipWith Fn.identity vecs

    fun zip3With f (xs, ys, zs) =
        let val len = Int.min (Int.min (length xs, length ys), length zs)
        in tabulate (len, fn i => f (sub (xs, i), sub (ys, i), sub (zs, i)))
        end

    fun sort cmp vs =
        let val arr = toArray vs
        in ArrayExt.sort cmp arr
         ; fromArray arr
        end

    fun stableSort cmp vs =
        let val arr = toArray vs
        in ArrayExt.stableSort cmp arr
         ; fromArray arr
        end

    fun inspect inspectEl vs =
        "#" ^ Int.toString (length vs) ^ "["
        ^ foldl (fn (v, res) => res ^ ", " ^ inspectEl v) "" vs ^ "]"
end
