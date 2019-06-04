signature CPS_TYPE = sig
    structure Prim: PRIM_TYPE

    type kind = FType.kind
    type param = FType.def

    datatype typ = FnT of {typeParams: param vector, paramTypes: typ vector}
                 | TParam of param
                 | Prim of Prim.t
end

signature CPS_TERM = sig
    type typ
    type label
    type param = {var: Name.t, typ: typ}

    datatype expr = PrimApp of primapp
                  | Param of param 
                  | Const of Const.t
    and primapp = IAdd of expr * expr

    datatype transfer = Goto of label * typ vector * expr vector
                      | If of expr * label * label
end

signature CPS_CONT = sig
    structure Type: CPS_TYPE
    structure Term: CPS_TERM

    type cont = { name: Name.t
                , typeParams: Type.param vector
                , valParams: Term.param vector
                , body: Term.transfer }
end

functor Cps (WordSortedMap: ORD_MAP where type Key.ord_key = word) :> sig
    structure Type: CPS_TYPE
    structure Term: CPS_TERM where type typ = Type.typ
    structure Cont: CPS_CONT

    type program
end = struct
    structure Type = struct
        structure Prim = FType.Prim

        type kind = FType.kind

        type param = FType.def

        datatype typ = FnT of {typeParams: param vector, paramTypes: typ vector}
                     | TParam of param
                     | Prim of Prim.t
    end

    structure Term = struct
        type typ = Type.typ

        type label = word

        type param = {var: Name.t, typ: Type.typ}

        datatype expr = PrimApp of primapp
                      | Param of param 
                      | Const of Const.t

        and primapp = IAdd of expr * expr

        datatype transfer = Goto of label * Type.typ vector * expr vector
                          | If of expr * label * label
    end

    structure Cont = struct
        structure Type = Type
        structure Term = Term

        type cont = { name: Name.t
                    , typeParams: Type.param vector
                    , valParams: Term.param vector
                    , body: Term.transfer }
    end

    type program = Cont.cont WordSortedMap.map
end

