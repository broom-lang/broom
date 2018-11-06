structure UnionFind :> sig
    type 'a t

    val new: 'a -> 'a t
    val union: 'a t -> 'a t -> unit

    val eq: 'a t -> 'a t -> bool
    val find: 'a t -> 'a t
    val content: 'a t -> 'a
end = struct
    datatype 'a node = Root of {content: 'a, rank: int}
                     | Link of 'a t
    withtype 'a t = 'a node ref

    fun new content = ref (Root {content = content, rank = 0})

    fun find u = case !u
                 of Root _ => u
                  | Link u' => let val res = find u'
                               in u := Link res
                                ; res
                               end

    fun union u u' = let val r = find u
                         val r' = find u'
                     in if r = r'
                        then ()
                        else case (!r, !r')
                             of ( Root {rank = rank, content = content}
                                , Root {rank = rank', content = _}) =>
                                 if rank < rank'
                                 then r := Link r'
                                 else ( r' := Link r
                                      ; r := Root { content = content
                                                  , rank = if rank = rank'
                                                           then rank + 1
                                                           else rank } )
                              | _ => raise Fail "unreachable"
                     end

    fun eq u u' = u = u'

    fun content u = case !(find u)
                    of Root {content = content, ...} => content
                     | _ => raise Fail "unreachable"
end
