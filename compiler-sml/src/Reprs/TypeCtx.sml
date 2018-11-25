structure TypeCtx :> sig
    type 't ctx

    val new: unit -> 't ctx

    val pushUv: 't ctx -> Name.t -> 't TypeVars.uv
    val pushUvs: 't ctx -> Name.t vector -> 't TypeVars.uv vector

    val findSrcType: 't ctx -> Name.t -> 't option

    val articulate2: 't ctx -> 't TypeVars.uv -> ('t TypeVars.uv * 't TypeVars.uv)

    val withOv: 't ctx -> Name.t -> (TypeVars.ov -> 'a) -> 'a
    val withMarker: 't ctx -> (unit -> 'a) -> 'a
    val withSrcType: 't ctx -> Name.t -> 't -> (unit -> 'a) -> 'a
    val withSrcTypes: 't ctx -> (Name.t * 't) vector -> (unit -> 'a) -> 'a
end = struct
    type 't ctx = { typeVars: 't TypeVars.env
                  , valTypes: 't ValTypes.env
                  , srcTypes: 't ValTypes.env }

    fun new () = { typeVars = TypeVars.newEnv ()
                 , valTypes = ValTypes.new ()
                 , srcTypes = ValTypes.new () }

    fun pushUv ({typeVars, ...}: 't ctx) = TypeVars.pushUv typeVars
    fun pushUvs ({typeVars, ...}: 't ctx) = TypeVars.pushUvs typeVars

    fun findSrcType ({srcTypes, ...}: 't ctx) name = ValTypes.find srcTypes name

    fun articulate2 ({typeVars, ...}: 't ctx) uv =
        let val names = Vector.fromList [Name.fresh (), Name.fresh ()]
            val uvs = TypeVars.insertUvsBefore typeVars uv names
        in (Vector.sub (uvs, 0), Vector.sub (uvs, 1))
        end

    fun withOv ({typeVars, ...}: 't ctx) name f =
        let val ov = TypeVars.pushOv typeVars name
            val res = f ov
        in TypeVars.popOv typeVars ov
         ; res
        end

    fun withMarker ({typeVars, ...}: 't ctx) f =
        let val marker = TypeVars.pushMarker typeVars
            val res = f ()
        in TypeVars.popMarker typeVars marker
         ; res
        end

    fun withSrcType ({srcTypes, ...}: 't ctx) name t f =
        let do ValTypes.insert srcTypes name t
            val res = f ()
        in ValTypes.remove srcTypes name
         ; res
        end

    fun withSrcTypes ({srcTypes, ...}: 't ctx) ext f =
        let do Vector.app (fn (name, t) => ValTypes.insert srcTypes name t) ext
            val res = f ()
        in Vector.app (ValTypes.remove srcTypes o #1) ext
         ; res
        end
end
