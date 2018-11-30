signature FAST_TYPE = sig
    datatype prim = datatype Type.prim

    datatype t = ForAll of Pos.t * def * t
               | UseT of Pos.t * def
               | Arrow of Pos.t * {domain: t, codomain: t}
               | Prim of Pos.t * prim
    withtype def = {name: Name.t, kind: t}

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

        datatype t = ForAll of Pos.t * def * t
                   | UseT of Pos.t * def
                   | Arrow of Pos.t * {domain: t, codomain: t}
                   | Prim of Pos.t * Type.prim
        withtype def = {name: Name.t, kind: t}

        fun eq _ = raise Fail "unimplemented"
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
