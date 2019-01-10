signature CPS_TYPE = sig
    datatype prim = datatype Type.prim

    datatype kind = datatype FAst.Type.kind

    datatype t = FnT of Pos.t * param vector * t vector 
               | ParamT of Pos.t * param
               | Prim of Pos.t * prim

    withtype param = {name: Name.t, kind: kind}
end

signature CPS_TERM = sig
    structure Type: CPS_TYPE

    datatype expr = Fn of Pos.t * Type.param vector * param vector * expr
                  | App of Pos.t * {callee: expr, argTypes: Type.t, args: expr vector}
                  | Param of Pos.t * param
                  | Const of Pos.t * Const.t

    withtype param = {name: Name.t, typ: Type.t}
end

structure CPS :> sig
    structure Type: CPS_TYPE

    structure Term: CPS_TERM where
        type Type.t = Type.t
end = struct
    structure Type = struct
        datatype prim = datatype Type.prim

        datatype kind = datatype FAst.Type.kind

        datatype t = FnT of Pos.t * param vector * t vector 
                   | ParamT of Pos.t * param
                   | Prim of Pos.t * prim

        withtype param = {name: Name.t, kind: kind}
    end

    structure Term = struct
        structure Type = Type

        datatype expr = Fn of Pos.t * Type.param vector * param vector * expr
                      | App of Pos.t * {callee: expr, argTypes: Type.t, args: expr vector}
                      | Param of Pos.t * param
                      | Const of Pos.t * Const.t

        withtype param = {name: Name.t, typ: Type.t}
    end
end

