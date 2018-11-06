structure Type :> sig
    type level

    val topLevel: level
    val pushLevel: level -> level

    datatype prim = Int

    datatype t = Arrow of t * t
               | UVar of var ref UnionFind.t
               | QVar of Name.t
               | Prim of prim
    and var = Unbound of Name.t * level
            | Bound of t
    
    type uv = var ref UnionFind.t

    datatype err = UnificationShapes of t * t
                 | Occurs of uv * t
    exception TypeError of err

    val fresh: level -> t

    val unify: t -> t -> unit
    val generalize: level -> t -> t
    val instantiate: level -> t -> t
end = struct
    type level = int

    val topLevel = 0
    fun pushLevel l = l + 1

    datatype prim = Int

    datatype t = Arrow of t * t
               | UVar of var ref UnionFind.t
               | QVar of Name.t
               | Prim of prim
    and var = Unbound of Name.t * level
            | Bound of t
    
    type uv = var ref UnionFind.t

    datatype err = UnificationShapes of t * t
                 | Occurs of uv * t
    exception TypeError of err

    fun fresh level = UVar (UnionFind.new (ref (Unbound (Name.fresh (), level))))

    fun occurs u t = 
        let val u = UnionFind.find u
            val l = case !(UnionFind.content u)
                    of Unbound (_, l) => l
                     | Bound _ => raise Fail "unreachable"
            val rec occurs' =
                fn Arrow (t, t') => (occurs' t; occurs' t')
                 | UVar u' => let val u' = UnionFind.find u
                              in if UnionFind.eq u u'
                                 then raise TypeError (Occurs (u, t))
                                 else let val r' = UnionFind.content u'
                                      in case !r'
                                         of Bound t' => occurs' t'
                                          | Unbound (name, l') =>
                                             r' := Unbound (name, Int.min (l, l'))
                                      end
                              end
                 | QVar _ => ()
                 | Prim _ => ()
        in occurs' t
        end

    fun assign u t = (occurs u t; UnionFind.content u := Bound t)

    fun unifyVar u t' = let val u = UnionFind.find u
                        in case !(UnionFind.content u)
                           of Bound t => unify t t'
                            | Unbound _ => assign u t'
                        end
                        
    and unify (Arrow (d, c)) (Arrow (d', c')) = (unify d d'; unify c c')
      | unify (UVar u) (UVar u') =
        if UnionFind.eq u u'
        then ()
        else let val u = UnionFind.find u
                 val u' = UnionFind.find u'
             in case (!(UnionFind.content u), !(UnionFind.content u'))
                of (Bound t, Bound t') => unify t t' (* Just some indirection *)
                 | (Unbound _, Bound t') => assign u t'
                 | (Bound t, Unbound _) => assign u' t
                 | (Unbound _, Unbound _) => UnionFind.union u u' (* Same, still variable *)
             end
      | unify (UVar u) t' = unifyVar u t'
      | unify t (UVar u') = unifyVar u' t
      | unify (t as QVar name) (t' as QVar name') =
        if name = name' then () else raise TypeError (UnificationShapes (t, t'))
      | unify (t as Prim pt) (t' as Prim pt') =
        if pt = pt' then () else raise TypeError (UnificationShapes (t, t'))
      | unify t t' = raise TypeError (UnificationShapes (t, t'))

    fun generalize level t =
        case t
        of Arrow (d, c) => let val d' = generalize level d
                               val c' = generalize level c
                           in if MLton.eq (d', d) andalso MLton.eq (c', c)
                              then t
                              else Arrow (d', c')
                           end
         | UVar u => (case !(UnionFind.content (UnionFind.find u))
                      of Bound t => t
                       | Unbound (name, l) => if l > level then QVar name else t)
         | QVar _ => t
         | Prim _ => t

    fun instantiate level t =
        let val uvars = NameHashTable.mkTable (0, Subscript)
            fun getUVar name =
                case NameHashTable.find uvars name
                of SOME uvar => uvar
                 | NONE => let val u = UVar (UnionFind.new (ref (Unbound (name, level))))
                           in NameHashTable.insert uvars (name, u)
                            ; u
                           end
            val rec inst = fn t as Arrow (d, c) => let val d' = inst d
                                                       val c' = inst c
                                                   in if MLton.eq (d', d) andalso MLton.eq (c', c)
                                                      then t
                                                      else Arrow (d', c')
                                                   end
                            | t as UVar _ => t
                            | QVar name => getUVar name
                            | t as Prim _ => t
        in inst t
        end
end