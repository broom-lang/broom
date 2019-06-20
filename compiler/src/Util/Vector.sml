structure Vector = struct
    open Vector

    fun zip (xs, ys) =
        let val {update, done, ...} =
                MLton.Vector.create (Int.min (Vector.length xs, Vector.length ys))
        in appi (fn (i, x) => update (i, (x, Vector.sub (ys, i)))) xs
         ; done ()
        end
end
