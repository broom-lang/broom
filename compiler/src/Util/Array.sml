structure Array = struct
    open Array

    fun clone arr = tabulate (length arr, fn i => sub (arr, i))

    fun mergeTo cmp target (ls, rs) =
        let fun fill i vs =
                ignore (ArraySlice.foldl (fn (v, i) =>
                                              ( ArraySlice.update (target, i, v)
                                              ; i + 1 ))
                                         i vs)

            fun doMerge i ls rs =
                case (ArraySlice.uncons ls, ArraySlice.uncons rs)
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

    fun mergeSortSlice cmp tmp vs =
        if ArraySlice.length vs > 1
        then let val mid = ArraySlice.length vs div 2
                 val ls = ArraySlice.subslice (vs, 0, SOME mid)
                 val ls' = ArraySlice.subslice (tmp, 0, SOME mid)
                 val rs = ArraySlice.subslice (vs, mid, NONE)
                 val rs' = ArraySlice.subslice (tmp, mid, NONE)
             in mergeSortSliceTo cmp ls' ls
              ; mergeSortSliceTo cmp rs' rs
              ; mergeTo cmp vs (ls', rs')
             end
        else ()

    and mergeSortSliceTo cmp target vs =
        if ArraySlice.length vs > 1
        then let val mid = ArraySlice.length vs div 2
                 val ls = ArraySlice.subslice (vs, 0, SOME mid)
                 val ls' = ArraySlice.subslice (target, 0, SOME mid)
                 val rs = ArraySlice.subslice (vs, mid, NONE)
                 val rs' = ArraySlice.subslice (target, mid, NONE)
             in mergeSortSlice cmp ls' ls
              ; mergeSortSlice cmp rs' rs
              ; mergeTo cmp target (ls, rs)
             end
        else ()

    fun mergeSort cmp arr =
        mergeSortSlice cmp (ArraySlice.full (clone arr)) (ArraySlice.full arr)

    val stableSort = mergeSort
end

