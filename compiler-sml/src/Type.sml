signature TYPE = sig
    structure TypeVars: TYPE_VARS

    type ov = TypeVars.ov

    datatype prim = Int
    
    datatype t = ForAll of Name.t * t
               | UseT of Name.t
               | OVar of ov
               | UVar of uv
               | Arrow of {domain: t, codomain: t}
               | Prim of prim
    withtype uv = t TypeVars.uv

    val primToString: prim -> string

    val isWellFormedType: t ValTypeCtx.env -> t -> bool
    val isWellFormedMonoType: t ValTypeCtx.env -> t -> bool
    val occurs: t TypeVars.uv -> t -> bool

    val substitute: Name.t * t -> t -> t
end 

structure Type :> TYPE = struct
    structure TypeVars = TypeVars

    val ovInScope = TypeVars.ovInScope
    val uvInScope = TypeVars.uvInScope
    val ovEq = TypeVars.ovEq
    val uvEq = TypeVars.uvEq

    type ov = TypeVars.ov

    datatype prim = Int
    
    datatype t = ForAll of Name.t * t
               | UseT of Name.t
               | OVar of ov
               | UVar of uv
               | Arrow of {domain: t, codomain: t}
               | Prim of prim
    withtype uv = t TypeVars.uv

    val primToString = fn Int => "Int"

    fun isWellFormedType annEnv =
        fn ForAll (param, t) => isWellFormedType (ValTypeCtx.insert annEnv param (UseT param)) t
         | UseT name => isSome (ValTypeCtx.find annEnv name)
         | OVar ov => ovInScope ov
         | UVar uv => uvInScope uv
         | Arrow {domain = d, codomain = c} =>
            isWellFormedType annEnv d andalso isWellFormedType annEnv c
         | Prim _ => true

    fun isWellFormedMonoType annEnv =
        fn ForAll _ => false
         | UseT name => isSome (ValTypeCtx.find annEnv name)
         | OVar ov => ovInScope ov
         | UVar uv => uvInScope uv
         | Arrow {domain = d, codomain = c} =>
            isWellFormedMonoType annEnv d andalso isWellFormedMonoType annEnv c
         | Prim _ => true

    fun occurs uv =
        fn ForAll (_, t) => occurs uv t
         | UseT _ => false
         | OVar _ => false
         | UVar uv' => uvEq (uv, uv')
         | Arrow {domain = d, codomain = c} => occurs uv d orelse occurs uv c
         | Prim _ => false

    fun substitute (name, st) =
        fn t as ForAll (name', t') => if name' = name
                                      then t
                                      else let val t'' = substitute (name, st) t'
                                           in if MLton.eq (t'', t')
                                              then t
                                              else ForAll (name', t'')
                                           end
         | t as UseT name' => if name' = name then st else t
         | t as OVar _ => t
         | t as UVar _ => t
         | t as Arrow {domain = d, codomain = c} => let val d' = substitute (name, st) d
                                                        val c' = substitute (name, st) c
                                                    in if MLton.eq (d', d) andalso MLton.eq (c', c)
                                                       then t
                                                       else Arrow {domain = d', codomain = c'}
                                                    end
         | t as Prim _ => t
end
