signature TYPE = sig
    structure TypeVars: TYPE_VARS

    type ov = TypeVars.ov

    datatype prim = Int
    
    datatype t = ForAll of Pos.t * Name.t * t
               | UseT of Pos.t * Name.t
               | OVar of Pos.t * ov
               | UVar of Pos.t * uv
               | Arrow of Pos.t * {domain: t, codomain: t}
               | Prim of Pos.t * prim
    withtype uv = t TypeVars.uv

    val primToString: prim -> string
    val toString: t -> string

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
    
    datatype t = ForAll of Pos.t * Name.t * t
               | UseT of Pos.t * Name.t
               | OVar of Pos.t * ov
               | UVar of Pos.t * uv
               | Arrow of Pos.t * {domain: t, codomain: t}
               | Prim of Pos.t * prim
    withtype uv = t TypeVars.uv

    val primToString = fn Int => "Int"

    val rec toString = fn ForAll (_, param, t) =>
                           "forall " ^ Name.toString param ^ " . " ^ toString t
                        | UseT (_, name) => Name.toString name
                        | OVar (_, ov) => Name.toString (TypeVars.ovName ov)
                        | UVar (_, uv) => Name.toString (TypeVars.uvName uv)
                        | Arrow (_, {domain, codomain}) =>
                           toString domain ^ " -> " ^ toString codomain
                        | Prim (_, p) => primToString p

    fun isWellFormedType annEnv =
        fn ForAll (pos, param, t) =>
            isWellFormedType (ValTypeCtx.insert annEnv param (UseT (pos, param))) t
         | UseT (_, name) => isSome (ValTypeCtx.find annEnv name)
         | OVar (_, ov) => ovInScope ov
         | UVar (_, uv) => uvInScope uv
         | Arrow (_, {domain = d, codomain = c}) =>
            isWellFormedType annEnv d andalso isWellFormedType annEnv c
         | Prim _ => true

    fun isWellFormedMonoType annEnv =
        fn ForAll _ => false
         | UseT (_, name) => isSome (ValTypeCtx.find annEnv name)
         | OVar (_, ov) => ovInScope ov
         | UVar (_, uv) => uvInScope uv
         | Arrow (_, {domain = d, codomain = c}) =>
            isWellFormedMonoType annEnv d andalso isWellFormedMonoType annEnv c
         | Prim _ => true

    fun occurs uv =
        fn ForAll (_, _, t) => occurs uv t
         | UseT _ => false
         | OVar _ => false
         | UVar (_, uv') => uvEq (uv, uv')
         | Arrow (_, {domain = d, codomain = c}) => occurs uv d orelse occurs uv c
         | Prim _ => false

    fun substitute (name, st) =
        fn t as ForAll (pos, name', t') =>
            if name' = name
            then t
            else let val t'' = substitute (name, st) t'
                 in if MLton.eq (t'', t')
                    then t
                    else ForAll (pos, name', t'')
                end
         | t as UseT (_, name') => if name' = name then st else t
         | t as OVar _ => t
         | t as UVar _ => t
         | t as Arrow (pos, {domain = d, codomain = c}) =>
            let val d' = substitute (name, st) d
                val c' = substitute (name, st) c
            in if MLton.eq (d', d) andalso MLton.eq (c', c)
               then t
               else Arrow (pos, {domain = d', codomain = c'})
            end
         | t as Prim _ => t
end
