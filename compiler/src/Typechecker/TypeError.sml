signature TYPE_ERROR = sig
    datatype t = UnCallable of TypecheckingCst.typ FAst.Term.expr * TypecheckingCst.typ
               | UnboundVal of Pos.t * Name.t
               | Occurs of (TypecheckingCst.scope, TypecheckingCst.typ) TypeVars.uv
                         * TypecheckingCst.typ
   
    exception TypeError of t

    val toString: t -> string
end

structure TypeError :> TYPE_ERROR = struct
    structure TC = TypecheckingCst

    datatype t = UnCallable of TypecheckingCst.typ FAst.Term.expr * TypecheckingCst.typ
               | UnboundVal of Pos.t * Name.t
               | Occurs of (TypecheckingCst.scope, TypecheckingCst.typ) TypeVars.uv
                         * TypecheckingCst.typ
    
    exception TypeError of t

    fun toString err =
        let val (pos, details) = case err
                                 of UnCallable (expr, typ) =>
                                     ( FAst.Term.exprPos expr
                                     , "Value " ^ FAst.Term.exprToString TC.Type.toString expr
                                           ^ " of type " ^ TC.Type.toString typ ^ " can not be called" )
                                  | UnboundVal (pos, name) => (pos, "Unbound variable " ^ Name.toString name)
                                  | Occurs (uv, t) =>
                                     ( TC.Type.pos t
                                     , "Occurs check: unifying " ^ Name.toString (TypeVars.uvName uv)
                                           ^ " with " ^ TC.Type.toString t ^ " would create infinite type" )
        in "TypeError in " ^ Pos.toString pos ^ ": " ^ details
        end
end

