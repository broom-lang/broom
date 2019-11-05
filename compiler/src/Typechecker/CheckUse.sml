structure CheckUse :> sig
    structure FType : CLOSED_FAST_TYPE where type sv = FlexFAst.Type.sv
    structure FTerm : FAST_TERM
        where type expr = FlexFAst.Term.expr
        where type Type.sv = FlexFAst.Type.sv
    structure Env : TYPECHECKING_ENV where type t = TypecheckingEnv.t

    val fix : { elaborateType : Env.t -> Cst.Type.typ -> FType.def list * FType.Concr.t
              , reAbstract : Env.t -> FType.Concr.t -> FType.Concr.t
              , instantiateExistential : Env.t -> FType.def vector * FType.Concr.t -> FType.Concr.t * FType.Concr.t vector
              , elaborateExpr : Env.t -> Cst.Term.expr -> FType.effect * FType.Concr.t * FTerm.expr }
           -> { unvisitedBindingType : Pos.span -> Env.t -> Name.t
                    -> Cst.Type.typ option Env.Bindings.Expr.def * Cst.Term.expr option -> FTerm.def
              , lookupValType : Cst.Term.expr -> Name.t -> Env.t -> FTerm.def option }
end = struct
    structure CTerm = Cst.Term
    datatype concr = datatype FType.concr
    structure FType = FlexFAst.Type
    structure FTerm = FlexFAst.Term
    structure Env = TypecheckingEnv
    structure Scope = Env.Scope
    datatype binding_state = datatype Env.Bindings.Expr.binding_state
    val subType = Subtyping.subType

    fun fix {elaborateType, reAbstract, instantiateExistential, elaborateExpr} =
        let fun unvisitedBindingType pos env name args : FTerm.def =
                let do Env.updateExpr pos env name (Fn.constantly (Visiting args)) (* Mark binding 'grey'. *)
                    val (def, binding') =
                        case args
                        of (def as {typ = SOME t, ...}, oexpr) =>
                            (case elaborateType env t
                             of ([], t) =>
                                 (FTerm.setDefTyp def t, Typed (FTerm.setDefTyp def (t, NONE), oexpr))
                              | (defs, t) =>
                                 (case Env.innermostScope env
                                  of Scope.InterfaceScope _ =>
                                      let val abst = Exists (valOf (Vector1.fromList defs), t)
                                          val t = reAbstract env abst (* OPTIMIZE *)
                                      in (FTerm.setDefTyp def t, Typed (FTerm.setDefTyp def (t, NONE), oexpr))
                                      end
                                   | _ =>
                                      let val (t, paths) =
                                              instantiateExistential env (Vector.fromList defs, t)
                                      in (FTerm.setDefTyp def t, Typed (FTerm.setDefTyp def (t, SOME paths), oexpr))
                                      end))
                         | (def as {typ = NONE, ...}, SOME expr) =>
                            let val (eff, t, expr) = elaborateExpr env expr (* FIXME: use `eff` *)
                                val def = FTerm.setDefTyp def t
                            in (def, Visited (def, SOME (eff, expr)))
                            end
                         | (def as {typ = NONE, ...}, oexpr as NONE) =>
                            let val t = FType.SVar (FType.UVar (Env.freshUv env))
                            in (FTerm.setDefTyp def t, Typed (FTerm.setDefTyp def (t, NONE), oexpr))
                            end
                in case valOf (Env.findExpr env name)
                   of Unvisited _ => raise Fail "unreachable" (* State is at 'least' `Visiting`. *)
                    | Visiting _ =>
                       ( Env.updateExpr pos env name (Fn.constantly binding')
                       ; def )
                    | Typed ({typ = (usageTyp, NONE), ...}, _) | Visited ({typ = usageTyp, ...}, _) =>
                       (* We must have found a cycle and used `cyclicBindingType`. *)
                       ( ignore (subType env pos (#typ def, usageTyp))
                       ; FTerm.setDefTyp def usageTyp )
                    | Typed ({typ = (_, SOME _), ...}, _) => raise Fail "unreachable"
                end
              
            (* In case we encounter a recursive reference to `name` not broken by type annotations we call
               this to insert a unification variable, inferring a monomorphic type. *)
            and cyclicBindingType pos env name (def, oexpr) : FTerm.def =
                let val t = FType.SVar (FType.UVar (Env.freshUv env))
                in Env.updateExpr pos env name (Fn.constantly (Typed ( FTerm.setDefTyp def (t, NONE)
                                                                     , oexpr )))
                 ; FTerm.setDefTyp def t
                end

            (* Get the type of the variable `name`, referenced at `pos`, from `env` by either
               - finding the type annotation (if available) (and elaborating it if not already done)
               - elaborating the expression bound to the variable (if available)
               - returning a fresh unification variable (if neither type annotation nor bound expression
                 is available or if a cycle is encountered) *)
            and lookupValType expr name env : FTerm.def option =
                Option.map (fn (Unvisited args, env) => unvisitedBindingType (CTerm.exprPos expr) env name args
                             | (Visiting args, env) =>
                                let val pos = CTerm.exprPos expr
                                in case Env.innermostScope env
                                   of Scope.InterfaceScope _ =>
                                       raise Fail ("Type cycle at " ^ Pos.spanToString (Env.sourcemap env) pos)
                                    | _ => cyclicBindingType pos env name args
                                end
                             | (Typed (def, _), _) => FTerm.updateDefTyp def #1
                             | (Visited (def, _), _) => def)
                           (Env.findExprClosure env name)
        in {unvisitedBindingType, lookupValType}
        end
end

