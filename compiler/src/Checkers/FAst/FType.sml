signature FAST_TYPE = sig
    structure Id: ID where type t = FTypeBase.Id.t
    structure Prim: PRIM_TYPE where type t = PrimType.t
    structure ScopeId: ID

    type kind = Kind.t

    type ('expr, 'error) env

    type def = FTypeBase.def

    datatype effect = datatype FTypeBase.effect
    type arrow = FTypeBase.arrow

    datatype concr' = datatype FTypeBase.concr
    datatype co' = datatype FTypeBase.co

    type sv
    type concr = sv FTypeBase.concr
    type co = sv FTypeBase.co

    val defToDoc: def -> PPrint.t
    val arrowDoc: arrow -> PPrint.t
    val svarToDoc: ('expr, 'error) env -> sv -> PPrint.t
    val rowExtBase: concr -> concr
    val kindDefault: kind -> concr

    structure Concr: sig
        type t = concr

        val toDoc: ('expr, 'error) env -> concr -> PPrint.t
        val substitute: ('expr, 'error) env -> concr Id.SortedMap.map -> concr -> concr
    end

    structure Co: sig
        val toDoc: ('expr, 'error) env -> co -> PPrint.t
    end
end

