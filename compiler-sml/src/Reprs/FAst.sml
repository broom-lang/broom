signature FAST_TYPE = sig
    datatype prim = datatype Type.prim

    datatype kind = TypeK
                  | ArrowK of Pos.t * {domain: kind, codomain: kind}

    and t = ForAll of Pos.t * def * t
          | UseT of Pos.t * def
          | Arrow of Pos.t * {domain: t, codomain: t}
          | Prim of Pos.t * prim
    withtype def = {name: Name.t, kind: kind}

    val kindEq: kind * kind -> bool
    val eq: t * t -> bool
end

structure FAst :> sig
    structure Type: FAST_TYPE

    datatype expr = Fn of Pos.t * def * expr
                  | TFn of Pos.t * Type.def * expr
                  | App of Pos.t * {callee: expr, arg: expr}
                  | TApp of Pos.t * {callee: expr, arg: Type.t}
                  | Use of Pos.t * def
                  | Const of Pos.t * Const.t

    and stmt = Def of Pos.t * def * expr

    withtype def = {name: Name.t, typ: Type.t}
end = struct
    structure Type = struct
        datatype prim = datatype Type.prim

        datatype kind = TypeK
                      | ArrowK of Pos.t * {domain: kind, codomain: kind}

        and t = ForAll of Pos.t * def * t
              | UseT of Pos.t * def
              | Arrow of Pos.t * {domain: t, codomain: t}
              | Prim of Pos.t * prim
        withtype def = {name: Name.t, kind: kind}

        val primEq = fn (Int, Int) => true

        val rec kindEq =
            fn (TypeK, TypeK) => true
             | ( ArrowK (_, {domain, codomain})
               , ArrowK (_, {domain = domain', codomain = codomain'}) ) =>
                kindEq (domain, domain') andalso kindEq (codomain, codomain')
             | _ => false

        fun eq args =
            let fun canonicalName names name = getOpt (NameSortedMap.find (names, name), name)
                fun eq' names =
                        fn ( ForAll (_, {name, kind}, body)
                           , ForAll (_, {name = name', kind = kind'}, body') ) =>
                            kindEq (kind, kind')
                            andalso eq' (NameSortedMap.insert (names, name', name))
                                        (body, body')
                         | (UseT (_, {name, kind}), UseT (_, {name = name', kind = kind'})) =>
                            kindEq (kind, kind')
                            andalso (canonicalName names name = canonicalName names name')
                         | ( Arrow (_, {domain, codomain})
                           , Arrow (_, {domain = domain', codomain = codomain'}) ) =>
                            eq' names (domain, domain') andalso eq' names (codomain, codomain')
                         | (Prim (_, p), Prim (_, p')) => primEq (p, p')
                         | _ => false
            in eq' NameSortedMap.empty args
            end
    end

    datatype expr = Fn of Pos.t * def * expr
                  | TFn of Pos.t * Type.def * expr
                  | App of Pos.t * {callee: expr, arg: expr}
                  | TApp of Pos.t * {callee: expr, arg: Type.t}
                  | Use of Pos.t * def
                  | Const of Pos.t * Const.t

    and stmt = Def of Pos.t * def * expr

    withtype def = {name: Name.t, typ: Type.t}
end
