structure ArraySlice = struct
    open ArraySlice

    fun uncons vs =
        if length vs > 0
        then SOME (sub (vs, 0), subslice (vs, 1, NONE))
        else NONE

    fun clone vs = full (Array.tabulate (length vs, fn i => sub (vs, i)))

    fun mergeTo cmp target (ls, rs) =
        let fun fill i vs =
                ignore (ArraySlice.foldl (fn (v, i) =>
                                              ( ArraySlice.update (target, i, v)
                                              ; i + 1 ))
                                         i vs)

            fun doMerge i ls rs =
                case (uncons ls, uncons rs)
                of (SOME (l, ls'), SOME (r, rs')) =>
                    (case cmp (l, r)
                     of LESS | EQUAL => 
                         ( ArraySlice.update (target, i, l)
                         ; doMerge (i + 1) ls' rs )
                      | GREATER =>
                         ( ArraySlice.update (target, i, r)
                         ; doMerge (i + 1) ls rs' ))
                 | (SOME (l, ls'), NONE) =>
                    ( ArraySlice.update (target, i, l)
                    ; fill (i + 1) ls' )
                 | (NONE, SOME (r, rs')) =>
                    ( ArraySlice.update (target, i, r)
                    ; fill (i + 1) rs' )
                 | (NONE, NONE) => ()
        in doMerge 0 ls rs
        end

    fun mergeSortTo cmp target vs =
        if ArraySlice.length vs > 1
        then let val mid = ArraySlice.length vs div 2
                 val ls = ArraySlice.subslice (vs, 0, SOME mid)
                 val ls' = ArraySlice.subslice (target, 0, SOME mid)
                 val rs = ArraySlice.subslice (vs, mid, NONE)
                 val rs' = ArraySlice.subslice (target, mid, NONE)
             in mergeSort cmp ls' ls
              ; mergeSort cmp rs' rs
              ; mergeTo cmp target (ls, rs)
             end
        else ()

    and mergeSort cmp tmp vs =
        if ArraySlice.length vs > 1
        then let val mid = ArraySlice.length vs div 2
                 val ls = ArraySlice.subslice (vs, 0, SOME mid)
                 val ls' = ArraySlice.subslice (tmp, 0, SOME mid)
                 val rs = ArraySlice.subslice (vs, mid, NONE)
                 val rs' = ArraySlice.subslice (tmp, mid, NONE)
             in mergeSortTo cmp ls' ls
              ; mergeSortTo cmp rs' rs
              ; mergeTo cmp vs (ls', rs')
             end
        else ()

    fun stableSort cmp vs = mergeSort cmp (clone vs) vs
end

