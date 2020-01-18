signature FAST_TYPE = sig
    structure Id: ID
        where type t = FTypeBase.Id.t
        where type 'v SortedMap.map = 'v FTypeBase.Id.SortedMap.map
    structure Prim: PRIM_TYPE where type t = PrimType.t
    structure ScopeId: ID

    type kind = Kind.t

    type def = FTypeBase.def

    datatype effect = datatype FTypeBase.effect
    type arrow = FTypeBase.arrow

    datatype concr' = datatype FTypeBase.concr
    datatype co' = datatype FTypeBase.co

    datatype sv = UVar of uv | Path of path
    withtype uv = sv FTypeBase.concr TypeVars.uv
    and path = sv FTypeBase.concr TypeVars.path

    type concr = sv FTypeBase.concr
    type row = sv FTypeBase.row
    type co = sv FTypeBase.co

    type ('expr, 'error) env = (concr, 'expr, 'error) TypecheckingEnv.t

    val defToDoc: def -> PPrint.t
    val arrowDoc: arrow -> PPrint.t
    val svarToDoc: ('expr, 'error) env -> sv -> PPrint.t
    val rowExtBase: concr -> concr
    val kindDefault: kind -> concr
    val primopType : Primop.t -> def vector * effect * {domain: concr vector, codomain: concr}

    structure Concr: sig
        type t = concr

        val toDoc: ('expr, 'error) env -> concr -> PPrint.t
        val toString : ('expr, 'error) env -> concr -> string
        val isSmall : concr -> bool
        val occurs : ('expr, 'error) env -> uv -> concr -> bool
        val substitute: ('expr, 'error) env -> concr Id.SortedMap.map -> concr -> concr
        val rewriteRow : Name.t -> concr -> row option
        val kindOf : (sv -> kind) -> concr -> kind
    end

    structure Co: sig
        val toDoc: ('expr, 'error) env -> co -> PPrint.t
    end
end

