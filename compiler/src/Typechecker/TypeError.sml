signature TYPE_ERROR = sig
    datatype t = UnCallable of TypecheckingCst.expr * TypecheckingCst.typ
               | UnboundVal of Pos.t * Name.t
               | Occurs of (TypecheckingCst.scope, TypecheckingCst.typ) TypeVars.uv
                         * TypecheckingCst.typ
   
    exception TypeError of t

    val toString: t -> string
end

structure TypeError :> TYPE_ERROR = struct
    structure TC = TypecheckingCst

    datatype t = UnCallable of TypecheckingCst.expr * TypecheckingCst.typ
               | UnboundVal of Pos.t * Name.t
               | Occurs of (TypecheckingCst.scope, TypecheckingCst.typ) TypeVars.uv
                         * TypecheckingCst.typ
    
    exception TypeError of t

    fun toString err =
        let val (pos, details) = case err
                                 of UnCallable (expr, typ) =>
                                     ( TC.exprPos expr
                                     , "Value " ^ TC.exprToString expr
                                           ^ " of type " ^ TC.typeToString typ ^ " can not be called" )
                                  | UnboundVal (pos, name) => (pos, "Unbound variable " ^ Name.toString name)
                                  | Occurs (uv, t) =>
                                     ( TC.Type.pos t
                                     , "Occurs check: unifying " ^ Name.toString (TypeVars.uvName uv)
                                           ^ " with " ^ TC.typeToString t ^ " would create infinite type" )
        in "TypeError in " ^ Pos.toString pos ^ ": " ^ details
        end
end

