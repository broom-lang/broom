structure Kindchecker :> sig
    structure FType : CLOSED_FAST_TYPE where type sv = FlexFAst.Type.sv
    type effect = FType.effect
    structure FTerm : FAST_TERM
        where type expr = FlexFAst.Term.expr
        where type Type.sv = FlexFAst.Type.sv
    structure Env : TYPECHECKING_ENV where type t = TypecheckingEnv.t
    type unvisited_binding_type =
         Pos.span -> Env.t -> Name.t -> Cst.Type.typ option Env.Bindings.Expr.def * Cst.Term.expr option -> FTerm.def

    val fix : { unvisitedBindingType : unvisited_binding_type
              , elaborateExpr : Env.t -> Cst.Term.expr -> FType.effect * FType.Concr.t * FTerm.expr }
           -> { reAbstract : Env.t -> FType.Abs.t -> FType.Concr.t
              , elaborateType : Env.t -> Cst.Type.typ -> FType.def list * FType.Concr.t
              , joinEffs : effect * effect -> effect }
end = struct
    structure CType = Cst.Type
    structure CTerm = Cst.Term
    datatype explicitness = datatype Cst.explicitness
    datatype effect = datatype FType.effect
    datatype abs = datatype FType.Abs.t
    structure FType = FlexFAst.Type
    structure FTerm = FlexFAst.Term
    structure Id = FType.Id
    structure Concr = FType.Concr
    datatype concr = datatype Concr.t
    val concr = FType.Abs.concr
    open TypeError
    structure Env = TypecheckingEnv
    structure Bindings = Env.Bindings
    datatype binding_state = datatype Bindings.Expr.binding_state
    structure Scope = Env.Scope
    val op|> = Fn.|>

    type unvisited_binding_type =
         Pos.span -> Env.t -> Name.t -> Cst.Type.typ option Env.Bindings.Expr.def * Cst.Term.expr option -> FTerm.def

    fun fix {unvisitedBindingType : unvisited_binding_type, elaborateExpr} =
        let fun reAbstract env =
                fn Exists (params, body) =>
                    let val (_, absBindings) = valOf (Env.nearestExists env)
                        val mapping =
                            Vector.foldl (fn ({var, kind}, mapping) =>
                                              let val args = Env.universalParams env
                                                  val kind = Vector.foldr (fn ({var = _, kind = argKind}, kind) =>
                                                                               FType.ArrowK { domain = argKind
                                                                                            , codomain = kind })
                                                                          kind args
                                                  val var' = Bindings.Type.fresh absBindings kind
                                                  val app = FType.app { callee = FType.UseT {var = var', kind}
                                                                      , args = Vector.map (fn def => FType.UseT def)
                                                                                          args }
                                              in Id.SortedMap.insert (mapping, var, app)
                                              end)
                                         Id.SortedMap.empty params
                    in Concr.substitute (Env.hasScope env) mapping body
                    end

            (* Elaborate the type `typ` and return the elaborated version. *)
            and elaborateType (env: Env.t) (t: CType.typ): FType.def list * concr =
                let val absBindings = Bindings.Type.new ()
                    val absScope = Scope.ExistsScope (Scope.Id.fresh (), absBindings)
                    val env = Env.pushScope env absScope

                    fun elaborate env =
                        fn CType.Pi (pos, {var, typ = domain}, expl, codomain) =>
                            let val (nonCallsiteTypeDefs, domain) =
                                    case domain
                                    of SOME domain => elaborateType env domain
                                     | NONE => ([], FType.SVar (FType.UVar (Env.freshUv env)))
                                val callsite = {var = FType.Id.fresh (), kind = FType.CallsiteK}
                                val typeDefs = callsite :: nonCallsiteTypeDefs

                                val env = Env.pushScope env (Scope.ForAllScope ( Scope.Id.fresh ()
                                                                               , typeDefs
                                                                                 |> Vector.fromList
                                                                                 |> Bindings.Type.fromDefs ))
                                val def = {pos = pos, id = DefId.fresh (), var, typ = domain}
                                val fnScope = Scope.FnScope (Scope.Id.fresh (), var, Visited (def, NONE))
                                val env = Env.pushScope env fnScope

                                val codomain = elaborate env codomain
                                val arrow = FType.Arrow (elaborateArr expl, {domain, codomain})
                                (* TODO: No callsite when `Implicit`: *) 
                                val typeDefs = if List.null nonCallsiteTypeDefs andalso FType.Concr.isSmall codomain
                                               then nonCallsiteTypeDefs
                                               else typeDefs
                            in case typeDefs
                               of [] => arrow
                                | _ => FType.ForAll (Vector.fromList typeDefs, arrow)
                            end
                         | CType.RecordT (pos, row) => FType.Record (elaborate env row)
                         | CType.RowExt (pos, {base, fields}) =>
                            let fun step ((label, t), base) =
                                    FType.RowExt {base, field = (label, elaborate env t)}
                            in Vector.foldl step (elaborate env base) fields
                            end
                         | CType.EmptyRow _ => FType.EmptyRow
                         | CType.WildRow _ =>
                            let val kind = FType.RowK
                                val var = Bindings.Type.fresh absBindings kind
                            in FType.UseT {var, kind}
                            end
                         | CType.Interface (pos, decls) =>
                            let val env = Env.pushScope env (declsScope env decls)
                                val fields = Vector.map (elaborateDecl env) decls
                                fun constructStep (field, base) = FType.RowExt {base, field}
                            in FType.Record (Vector.foldl constructStep FType.EmptyRow fields)
                            end
                         | CType.Path pathExpr =>
                            let val (eff, t, _) = elaborateExpr env pathExpr
                            in case eff
                               of Pure =>
                                   (case t
                                    of FType.Type t => reAbstract env t
                                     | _ => raise Fail ("Type path " ^ CTerm.exprToString pathExpr
                                                    ^ "does not denote type at "
                                                    ^ Pos.spanToString (Env.sourcemap env) (CTerm.exprPos pathExpr)))
                                | _ => raise Fail "Impure type path expression"
                            end
                         | CType.TypeT pos =>
                            let val args = Env.universalParams env
                                val kind = Vector.foldr (fn ({var = _, kind = argKind}, kind) =>
                                                             FType.ArrowK {domain = argKind, codomain = kind})
                                                        FType.TypeK args
                                val var = Bindings.Type.fresh absBindings kind
                                val app = FType.app { callee = FType.UseT {var, kind}
                                                    , args = Vector.map (fn def => FType.UseT def)
                                                                        args }
                            in FType.Type (concr app)
                            end
                         | CType.Singleton (_, expr) =>
                            (case elaborateExpr env expr
                             of (Pure, t, _) => t
                              | _ => raise Fail "Impure singleton type expression")
                         | CType.Prim (pos, p) => FType.Prim p

                    and elaborateDecl env (_, name, _) =
                        ( name
                        , case valOf (Env.findExpr env name) (* `name` is in `env` by construction *)
                          of Unvisited args => #typ (unvisitedBindingType (CType.pos t) env name args)
                           | Visiting _ =>
                              raise Fail ("Type cycle at " ^ Pos.spanToString (Env.sourcemap env) (CType.pos t))
                           | Typed ({typ = (typ, _), ...}, _) | Visited ({typ, ...}, _) => typ )

                    val t = elaborate env t
                    val defs = Bindings.Type.defs absBindings
                in (defs, t)
                end

            and elaborateArr arr =
                case arr
                of Implicit => Implicit
                 | Explicit eff => Explicit (elaborateEff eff)

            and elaborateEff eff =
                case eff
                of Cst.Pure => Pure
                 | Cst.Impure => Impure

            and joinEffs effs =
                case effs
                of (Pure, Pure) => Pure
                 | (Pure, Impure) => Impure
                 | (Impure, Pure) => Impure
                 | (Impure, Impure) => Impure

            and declsScope env decls =
                let val builder = Bindings.Expr.Builder.new ()
                    do Vector.app (fn (pos, var, t) =>
                                       let val def = {pos, id = DefId.fresh (), var, typ = SOME t}
                                       in Bindings.Expr.Builder.insert builder pos var (Unvisited (def, NONE))
                                          handle TypeError err => Env.error env err
                                       end)
                                  decls
                in Scope.InterfaceScope (Scope.Id.fresh (), Bindings.Expr.Builder.build builder)
                end
        in {reAbstract, elaborateType, joinEffs}
        end
end

