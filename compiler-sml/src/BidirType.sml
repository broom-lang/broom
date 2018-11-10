functor BidirType(TypeVars: TYPE_VARS) :> sig
    structure TypeVars: TYPE_VARS

    type ov = TypeVars.ov

    datatype prim = Int
    
    datatype t = ForAll of ov * t
               | OVar of ov
               | UVar of uv
               | Arrow of {domain: t, codomain: t}
               | Prim of prim
    withtype uv = t TypeVars.uv

    val isWellFormedType: t TypeVars.env -> t -> bool
    val isWellFormedMonoType: t TypeVars.env -> t -> bool
    val occurs: t TypeVars.uv -> t -> bool

    val substitute: t TypeVars.uv -> TypeVars.ov -> t -> t
end = struct
    structure TypeVars = TypeVars

    val ovInScope = TypeVars.ovInScope
    val uvInScope = TypeVars.uvInScope
    val uvEq = TypeVars.uvEq

    type ov = TypeVars.ov

    datatype prim = Int
    
    datatype t = ForAll of ov * t
               | OVar of ov
               | UVar of uv
               | Arrow of {domain: t, codomain: t}
               | Prim of prim
    withtype uv = t TypeVars.uv

    fun isWellFormedType env =
        fn ForAll (ov, t) => let val _ = TypeVars.pushOv' env ov
                                 val res = isWellFormedType env t
                             in TypeVars.popOv env ov
                              ; res
                             end
         | OVar ov => ovInScope env ov
         | UVar uv => uvInScope env uv
         | Arrow {domain = d, codomain = c} =>
            isWellFormedType env d andalso isWellFormedType env c
         | Prim _ => true

    fun isWellFormedMonoType env =
        fn ForAll _ => false
         | OVar ov => ovInScope env ov
         | UVar uv => uvInScope env uv
         | Arrow {domain = d, codomain = c} =>
            isWellFormedMonoType env d andalso isWellFormedMonoType env c
         | Prim _ => true

    fun occurs uv =
        fn ForAll (_, t) => occurs uv t
         | OVar _ => false
         | UVar uv' => uvEq uv uv'
         | Arrow {domain = d, codomain = c} => occurs uv d orelse occurs uv c
         | Prim _ => false

    fun substitute uv ov =
        fn t as ForAll (ov', t') => if ov' = ov
                                    then t
                                    else let val t'' = substitute uv ov t'
                                         in if MLton.eq (t'', t')
                                            then t
                                            else ForAll (ov', substitute uv ov t')
                                         end
         | t as OVar ov' => if ov' = ov then UVar uv else t
         | t as UVar _ => t
         | t as Arrow {domain = d, codomain = c} => let val d' = substitute uv ov d
                                                        val c' = substitute uv ov c
                                                    in if MLton.eq (d', d) andalso MLton.eq (c', c)
                                                       then t
                                                       else Arrow {domain = d', codomain = c'}
                                                    end
         | t as Prim _ => t
end
