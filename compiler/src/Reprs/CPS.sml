signature CPS_TYPE = sig
    datatype prim = datatype Type.prim

    datatype kind = datatype FAst.Type.kind

    datatype t = FnT of Pos.t * param vector * t vector 
               | ParamT of Pos.t * param
               | Prim of Pos.t * prim

    withtype param = {name: Name.t, kind: kind}

    val kindToString: kind -> string
    val paramToString: param -> string
    val toString: t -> string
end

signature CPS_TERM = sig
    structure Type: CPS_TYPE

    datatype expr = Fn of Pos.t * Type.param vector * param vector * expr
                  | App of Pos.t * {callee: expr, argTypes: Type.t vector, args: expr vector}
                  | Param of Pos.t * param
                  | Const of Pos.t * Const.t

    withtype param = {name: Name.t, typ: Type.t}

    val paramToString: param -> string
    val toString: expr -> string
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

        val kindToString = FAst.Type.kindToString
        val paramToString = FAst.Type.defToString
        val rec toString =
            fn FnT (_, typeParams, paramTypes) =>
                "\\/ " ^ Vector.foldl (fn (param, acc) => acc ^ paramToString param ^ ", ")
                                      "" typeParams
                ^ "fn " ^ Vector.foldl (fn (param, acc) => acc ^ toString param ^ ", ")
                                       "" paramTypes
             | ParamT (_, {name, ...}) => Name.toString name
             | Prim (_, prim) => Type.primToString prim
    end

    structure Term = struct
        structure Type = Type

        datatype expr = Fn of Pos.t * Type.param vector * param vector * expr
                      | App of Pos.t * {callee: expr, argTypes: Type.t vector, args: expr vector}
                      | Param of Pos.t * param
                      | Const of Pos.t * Const.t

        withtype param = {name: Name.t, typ: Type.t}

        fun paramToString {name, typ} = Name.toString name ^ ": " ^ Type.toString typ
        
        val rec toString =
            fn Fn (_, typeParams, params, body) =>
                "/\\ " ^ Vector.foldl (fn (param, acc) => acc ^ Type.paramToString param ^ ", ")
                                      "" typeParams
                ^ "fn " ^ Vector.foldl (fn (param, acc) => acc ^ paramToString param ^ ", ")
                                       "" params
                ^ toString body
             | App (_, {callee, argTypes, args}) =>
                toString callee ^ "[" ^ Vector.foldl (fn (typeArg, acc) => acc ^ Type.toString typeArg ^ ", ")
                                                     "" argTypes ^ "]"
                ^ "(" ^ Vector.foldl (fn (arg, acc) => acc ^ toString arg ^ ", ") "" args ^ ")"
             | Param (_, {name, ...}) => Name.toString name
             | Const (_, c) => Const.toString c
    end
end

