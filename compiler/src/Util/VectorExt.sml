structure VectorExt :> sig
    val push: 'a vector * 'a -> 'a vector
end = struct
    fun push (vec, last) =
        let val {update = update, done = done, ...} = MLton.Vector.create (Vector.length vec + 1)
        in Vector.appi (fn (i, v) => update (i, v)) vec
         ; update (Vector.length vec, last)
         ; done ()
        end
end