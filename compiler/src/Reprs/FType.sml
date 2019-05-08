functor FType(Var: sig
    type t 
    val toString: t -> string
end) = struct
    datatype prim = Unit | I32

    datatype kind = ArrowK of Pos.t * {domain: kind, codomain: kind}
                  | TypeK of Pos.t

    type def = {var: Var.t, kind: kind}

    datatype 'typ typ = ForAll of Pos.t * def * 'typ
                      | Arrow of Pos.t * {domain: 'typ, codomain: 'typ}
                      | Type of Pos.t * 'typ
                      | UseT of Pos.t * def
                      | Prim of Pos.t * prim

    val rec kindToString =
        fn TypeK _ => "Type"
         | ArrowK (_, {domain, codomain}) =>
            kindToString domain ^ " -> " ^ kindToString codomain

    val primToString = fn Unit => "()"
                        | I32 => "I32"

    fun defToString {var, kind} = Var.toString var ^ ": " ^ kindToString kind

    fun toString toString =
        fn ForAll (_, param, t) =>
            "forall " ^ defToString param ^ " . " ^ toString t
         | Arrow (_, {domain, codomain}) =>
            toString domain ^ " -> " ^ toString codomain
         | Type (_, t) => "[= " ^ toString t ^ "]"
         | UseT (_, def) => defToString def 
         | Prim (_, p) => primToString p

    val pos =
        fn ForAll (pos, _, _) => pos
         | Arrow (pos, _) => pos
         | Type (pos, _) => pos
         | UseT (pos, _) => pos
         | Prim (pos, _) => pos

    fun shallowFoldl f acc =
        fn ForAll (_, _, t) => f (t, acc)
         | Arrow (_, {domain, codomain}) => f (codomain, f (domain, acc))
         | Type (_, t) => f (t, acc)
         | UseT _ | Prim _ => acc
end

structure NameFType = FType(Name)

