functor BidirType(TypeVars: TYPE_VARS) :> sig
    datatype prim = Int
    
    datatype t = ForAll of TypeVars.ov * t
               | OVar of TypeVars.ov
               | UVar of t TypeVars.uv
               | Arrow of {domain: t, codomain: t}
               | Prim of prim

    val isWellFormedMonoType: t TypeVars.env -> t -> bool
    val occurs: t TypeVars.uv -> t -> bool
end = struct
    val ovInScope = TypeVars.ovInScope
    val uvInScope = TypeVars.uvInScope
    val uvEq = TypeVars.uvEq

    datatype prim = Int
    
    datatype t = ForAll of TypeVars.ov * t
               | OVar of TypeVars.ov
               | UVar of t TypeVars.uv
               | Arrow of {domain: t, codomain: t}
               | Prim of prim

    fun isWellFormedMonoType env =
        fn ForAll (ov, t) => let val _ = TypeVars.pushOv' env ov
                                 val res = isWellFormedMonoType env t
                             in TypeVars.popOv env ov
                              ; res
                             end
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
end
