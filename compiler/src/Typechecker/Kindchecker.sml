structure Kindchecker :> sig
    structure FType : CLOSED_FAST_TYPE where type sv = FlexFAst.Type.sv
    type effect = FType.effect
    structure FTerm : FAST_TERM
        where type expr = FlexFAst.Term.expr
        where type Type.sv = FlexFAst.Type.sv
    type env = (FType.concr, FTerm.expr, TypeError.t) TypecheckingEnv.t
    type unvisited_binding_type =
         Pos.span -> env -> Name.t -> Cst.Type.typ option TypecheckingEnv.Bindings.Expr.def * Cst.Term.expr option -> FTerm.def

    val reAbstract : env -> FType.Concr.t -> FType.Concr.t
    val fix : { unvisitedBindingType : unvisited_binding_type
              , elaborateExpr : env -> Cst.Term.expr -> FType.effect * FType.Concr.t * FTerm.expr }
           -> (env -> Cst.Type.typ -> FType.def list * FType.Concr.t)
end = struct
    structure CType = Cst.Type
    structure CTerm = Cst.Term
    datatype explicitness = datatype Cst.explicitness
    datatype effect = datatype FType.effect
    datatype concr = datatype FType.concr
    structure FType = FlexFAst.Type
    structure FTerm = FlexFAst.Term
    structure Id = FType.Id
    structure Concr = FType.Concr
    datatype concr = datatype Concr.t
    datatype sv = datatype FType.sv
    structure Uv = TypeVars.Uv
    structure Path = TypeVars.Path
    open TypeError
    structure Env = TypecheckingEnv
    structure Bindings = Env.Bindings
    datatype binding_state = datatype Bindings.Expr.binding_state
    structure Scope = Env.Scope
    type env = (FType.concr, FTerm.expr, TypeError.t) Env.t
    val instantiate = TypecheckingOps.instantiate
    val subType = Subtyping.subType
    datatype either = datatype Either.t
    val op|> = Fn.|>

    fun rowWhere env pos (row, field' as (label', _)) =
        let val rec override =
                fn RowExt {base, field = field as (label, _)} =>
                    if label = label'
                    then let val params = Env.existentialParams env (* FIXME: only the params used in `fieldt` *)
                         in  instantiate env (params, row) (fn (env, _, row) =>
                                 TypecheckingOps.rowWhere (fn env => fn pos => fn base => fn label => fn (sub, super) =>
                                     ( subType env pos (sub, super)
                                     ; RowExt {base, field = (label, sub)} )
                                 ) env pos (row, field')
                             )
                         end
                    else override base
        in override row
        end
 
    type unvisited_binding_type =
         Pos.span -> env -> Name.t -> Cst.Type.typ option Env.Bindings.Expr.def * Cst.Term.expr option -> FTerm.def

    fun reAbstract env =
        fn Exists (params, body) =>
            let val (_, absBindings) = valOf (Env.nearestExists env)
                val mapping =
                    Vector1.foldl (fn ({var, kind}, mapping) =>
                                       let val args = Env.universalParams env
                                           val kind = Vector.foldr (fn ({var = _, kind = argKind}, kind) =>
                                                                        FType.ArrowK { domain = argKind
                                                                                     , codomain = kind })
                                                                   kind args
                                           val var' = Bindings.Type.fresh absBindings kind
                                           val use =
                                               case Vector1.fromVector args
                                               of SOME args =>
                                                   FType.App { callee = FType.UseT {var = var', kind}
                                                             , args = Vector1.map (fn def => FType.UseT def)
                                                                                  args }
                                                | NONE => FType.UseT {var = var', kind}
                                       in Id.SortedMap.insert (mapping, var, use)
                                       end)
                                  Id.SortedMap.empty params
            in Concr.substitute env mapping body
            end
         | t => t

    fun fix {unvisitedBindingType : unvisited_binding_type, elaborateExpr} =
            (* Elaborate the type `typ` and return the elaborated version. *)
        let fun elaborateType (env: env) (t: CType.typ): FType.def list * concr =
                let val absBindings = Bindings.Type.new ()
                    val absScope = Scope.ExistsScope (Scope.Id.fresh (), absBindings)
                    val env = Env.pushScope env absScope

                    fun elaborate env =
                        fn CType.Pi (pos, {var, typ = domain}, expl, codomain) =>
                            let val (nonCallsiteTypeDefs, domain) =
                                    case domain
                                    of SOME domain => elaborateType env domain
                                     | NONE => ([], FType.SVar (FType.UVar (TypeVars.Uv.fresh env FType.TypeK)))
                                val callsite = {var = FType.Id.fresh (), kind = FType.CallsiteK}
                                val typeDefs = callsite :: nonCallsiteTypeDefs

                                val env = Env.pushScope env (Scope.ForAllScope ( Scope.Id.fresh ()
                                                                               , typeDefs
                                                                                 |> Vector1.fromList
                                                                                 |> valOf
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
                            in case Vector1.fromList typeDefs
                               of SOME params => FType.ForAll (params, arrow)
                                | NONE => arrow
                            end
                         | CType.RecordT (_, row) => FType.Record (elaborate env row)
                         | CType.RowExt (pos, {base, edits}) =>
                            let fun elaborateEdit (edit, base) =
                                    let val (step, fields) =
                                            case edit
                                            of CType.WithT fields =>
                                                ( fn ((label, t), base) =>
                                                      FType.RowExt {base, field = (label, elaborate env t)}
                                                , fields )
                                             | CType.WhereT fields =>
                                                ( fn ((label, t), base) =>
                                                      rowWhere env pos (base, (label, elaborate env t))
                                                , fields )
                                    in Vector.foldl step base fields
                                    end
                            in Vector.foldl elaborateEdit (elaborate env base) edits
                            end
                         | CType.EmptyRow _ => FType.EmptyRow
                         | CType.WildRow _ =>
                            let val kind = FType.RowK
                                val var = Bindings.Type.fresh absBindings kind
                            in FType.UseT {var, kind}
                            end
                         | CType.Interface (pos, super, specs) =>
                            let val (superRow, env) =
                                    case super
                                    of SOME {var, typ} =>
                                        (case elaborate env typ
                                         of typ as FType.Record row =>
                                             (case var
                                              of SOME var =>
                                                  let val def = {pos, id = DefId.fresh (), var, typ = (typ, NONE)}
                                                  in ( row
                                                     , Env.pushScope env (Scope.PatternScope ( Scope.Id.fresh ()
                                                                                             , var
                                                                                             , Typed (def, NONE) )) )
                                                  end
                                               | NONE => (row, env))
                                          | _ => raise Fail "unimplemented")
                                     | NONE => (FType.EmptyRow, env)
                                
                                val env = Env.pushScope env (declsScope env specs)
                                val row =
                                    Vector.foldl (fn (Cst.Extend decl, base) =>
                                                      FType.RowExt {base, field = elaborateDecl env decl}
                                                   | (Cst.Override (decl as (pos, _, _)), base) =>
                                                      rowWhere env pos (base, elaborateDecl env decl))
                                                 superRow specs
                            in FType.Record row
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
                         | CType.TypeT _ =>
                            let val args = Env.universalParams env
                                val kind = Vector.foldr (fn ({var = _, kind = argKind}, kind) =>
                                                             FType.ArrowK {domain = argKind, codomain = kind})
                                                        FType.TypeK args
                                val var = Bindings.Type.fresh absBindings kind
                                val use =
                                    case Vector1.fromVector args
                                    of SOME args =>
                                        FType.App { callee = FType.UseT {var, kind}
                                                  , args = Vector1.map (fn def => FType.UseT def)
                                                                       args }
                                     | NONE => FType.UseT {var, kind}
                            in FType.Type use 
                            end
                         | CType.Singleton (_, expr) =>
                            (case elaborateExpr env expr
                             of (Pure, t, _) => t
                              | _ => raise Fail "Impure singleton type expression")
                         | CType.Prim (_, p) => FType.Prim p

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

            and declsScope env decls =
                let val builder = Bindings.Expr.Builder.new ()
                    do Vector.app (fn Cst.Extend (pos, var, t) | Cst.Override (pos, var, t) =>
                                       let val def = {pos, id = DefId.fresh (), var, typ = SOME t}
                                       in case Bindings.Expr.Builder.insert builder pos var (Unvisited (def, NONE))
                                          of Left err => Env.error env (DuplicateBinding err)
                                           | Right res => res
                                       end
                                    | Cst.Exclude _ => ())
                                  decls
                in Scope.InterfaceScope (Scope.Id.fresh (), Bindings.Expr.Builder.build builder)
                end
        in elaborateType
        end

    and elaborateArr Implicit = Implicit
      | elaborateArr (Explicit eff) = Explicit (elaborateEff eff)

    and elaborateEff Cst.Pure = Pure
      | elaborateEff Cst.Impure = Impure
end

