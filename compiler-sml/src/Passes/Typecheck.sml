structure Typecheck :> sig
    datatype error = UvOutOfScope of Name.t
                   | OvOutOfScope of Name.t
                   | Unbound of Name.t
                   | UnboundType of Name.t
                   | Occurs of Type.t Type.TypeVars.uv * Type.t
                   | Uncallable of Cst.expr * Type.t
                   | TypeMismatch of Type.t * Type.t
                   | MalformedType of Type.t

    val errorToString: error -> string

    val typecheck: Cst.stmt vector -> (error, Cst.stmt vector) Either.t
end = struct
    structure TypeVars = Type.TypeVars

    datatype error = UvOutOfScope of Name.t
                   | OvOutOfScope of Name.t
                   | Unbound of Name.t
                   | UnboundType of Name.t
                   | Occurs of Type.t Type.TypeVars.uv * Type.t
                   | Uncallable of Cst.expr * Type.t
                   | TypeMismatch of Type.t * Type.t
                   | MalformedType of Type.t

    exception TypeError of error

    val errorToString = fn UvOutOfScope name => "UvOutOfScope: " ^ Name.toString name
                         | OvOutOfScope name => "OvOutOfScope: " ^ Name.toString name
                         | Unbound name => "Unbound: " ^ Name.toString name
                         | UnboundType name => "UnboundType: " ^ Name.toString name
                         | Occurs (uv, t) =>
                            "Occurs: " ^ Name.toString (TypeVars.uvName uv) ^ " " ^ Type.toString t
                         | Uncallable (expr, t) =>
                            "Uncallable: " ^ Cst.exprToString expr ^ ": " ^ Type.toString t
                         | TypeMismatch (t, t') =>
                            "TypeMismatch: " ^ Type.toString t ^ " " ^ Type.toString t'
                         | MalformedType t => "MalformedType: " ^ Type.toString t

    datatype lattice_y = Sub | Super

    val flipY = fn Sub => Super
                 | Super => Sub

    fun withOv tenv name f = let val ov = TypeVars.pushOv tenv name
                                 val res = f ov
                             in TypeVars.popOv tenv ov
                              ; res
                             end

    fun withMarker tenv f = let val marker = TypeVars.pushMarker tenv
                                val res = f ()
                            in TypeVars.popMarker tenv marker
                             ; res
                            end

    fun articulate tenv uv =
        let val cuv = TypeVars.insertUvBefore tenv uv (Name.fresh ())
            val duv = TypeVars.insertUvBefore tenv uv (Name.fresh ())
        in (duv, cuv)
        end

    fun annFreeVars annEnv =
        fn Type.ForAll (pos, param, t) =>
            annFreeVars (ValTypeCtx.insert annEnv param (Type.UseT (pos, param))) t
         | Type.UseT (_, name) => if isSome (ValTypeCtx.find annEnv name)
                                  then NameSortedSet.empty
                                  else NameSortedSet.fromList [name]
         | Type.OVar _ => NameSortedSet.empty
         | Type.UVar _ => NameSortedSet.empty
         | Type.Arrow (_, {domain, codomain}) =>
            NameSortedSet.union (annFreeVars annEnv domain, annFreeVars annEnv codomain)
         | Type.Prim _ => NameSortedSet.empty

    fun hydrate annEnv =
        fn Type.ForAll (pos, param, t) =>
            Type.ForAll ( pos, param
                        , hydrate (ValTypeCtx.insert annEnv param (Type.UseT (pos, param))) t )
         | Type.UseT (_, name) => (case ValTypeCtx.find annEnv name
                                   of SOME t => t
                                    | NONE => raise TypeError (UnboundType name))
         | t as Type.OVar _ => t
         | t as Type.UVar _ => t
         | Type.Arrow (pos, {domain, codomain}) =>
            Type.Arrow (pos, {domain = hydrate annEnv domain, codomain = hydrate annEnv codomain})
         | t as Type.Prim (pos, p) => t

    fun hydrateBinder tenv pos annEnv ann =
        let val fvs = annFreeVars annEnv ann
            fun step (fv, annEnv) = let val uv = TypeVars.pushUv tenv fv
                                    in ValTypeCtx.insert annEnv fv (Type.UVar (pos, uv))
                                    end
            val annEnv = NameSortedSet.foldl step annEnv fvs
        in (hydrate annEnv ann, annEnv)
        end

    fun hydrateBinders tenv annEnv anns =
        let val fvs = Vector.foldl (fn (ann, fvs) =>
                                        NameSortedSet.union (annFreeVars annEnv ann, fvs))
                                   NameSortedSet.empty anns
            val fvs = Vector.fromList (NameSortedSet.toList fvs)
            val uvs = TypeVars.pushUvs tenv fvs
            fun step (i, fv, annEnv) = let val pos = Type.pos (Vector.sub (anns, i))
                                           val uv = Vector.sub (uvs, i)
                                       in ValTypeCtx.insert annEnv fv (Type.UVar (pos, uv))
                                       end
            val annEnv = Vector.foldli step annEnv fvs
        in (Vector.map (hydrate annEnv) anns, annEnv)
        end
    
    fun checkConst pos = fn c as Const.Int _ => (c, Type.Prim (pos, Type.Int))

    fun typecheck program =
        let val tenv = TypeVars.newEnv ()

            fun assignForSome pos annEnv param y uv t =
                case y
                of Sub => withOv tenv param (fn ov =>
                              assign annEnv y uv (Type.substitute (param, Type.OVar (pos, ov)) t)
                          )
                 | Super => withMarker tenv (fn () =>
                                let val uv' = TypeVars.pushUv tenv (Name.fresh ())
                                in assign annEnv y uv (Type.substitute ( param
                                                                       , Type.UVar (pos, uv') ) t)
                                end
                            )

            and assign annEnv y uv t =
                let fun doassign annEnv uv =
                        fn Type.ForAll (pos, param, t') => assignForSome pos annEnv param y uv t'
                         | t as Type.UseT _ => raise Fail "unreachable"
                         | t as Type.OVar _ => TypeVars.uvSet uv t
                         | Type.UVar (pos, uv') => (case TypeVars.uvGet uv'
                                                    of Either.Left uv' => TypeVars.uvMerge uv uv'
                                                     | Either.Right t => doassign annEnv uv t)
                         | Type.Arrow (_, {domain, codomain}) =>
                            let val (duv, cuv) = articulate tenv uv
                            in assign annEnv (flipY y) duv domain
                             ; assign annEnv y cuv codomain
                            end
                         | t as Type.Prim _ => TypeVars.uvSet uv t
                in if TypeVars.uvInScope uv
                   then if Type.occurs uv t
                        then raise TypeError (Occurs (uv, t))
                        else doassign annEnv uv t
                   else raise TypeError (UvOutOfScope (TypeVars.uvName uv))
                end

            fun checkSub annEnv (Type.UVar (_, uv)) (Type.UVar (_, uv')) =
                (case (TypeVars.uvGet uv, TypeVars.uvGet uv')
                 of (Either.Left uv, Either.Left uv') =>
                     if TypeVars.uvInScope uv
                     then if TypeVars.uvInScope uv'
                          then if TypeVars.uvEq (uv, uv') then () else TypeVars.uvMerge uv uv'
                          else raise TypeError (UvOutOfScope (TypeVars.uvName uv'))
                     else raise TypeError (UvOutOfScope (TypeVars.uvName uv))
                  | (Either.Left uv, Either.Right t') => assign annEnv Sub uv t'
                  | (Either.Right t, Either.Left uv') => assign annEnv Super uv' t
                  | (Either.Right t, Either.Right t') => checkSub annEnv t t')
              | checkSub annEnv (Type.UVar (_, uv)) t' =
                (case TypeVars.uvGet uv
                 of Either.Left uv => assign annEnv Sub uv t'
                  | Either.Right t => checkSub annEnv t t')
              | checkSub annEnv t (Type.UVar (_, uv')) =
                (case TypeVars.uvGet uv'
                 of Either.Left uv' => assign annEnv Super uv' t
                  | Either.Right t' => checkSub annEnv t t')
              | checkSub annEnv t (Type.ForAll (pos, param, t')) =
                withOv tenv param (fn ov =>
                    checkSub annEnv t (Type.substitute (param, Type.OVar (pos, ov)) t')
                )
              | checkSub annEnv (Type.ForAll (pos, ov, t)) t' =
                withMarker tenv (fn () =>
                    let val uv = TypeVars.pushUv tenv (Name.fresh ())
                    in checkSub annEnv (Type.substitute (ov, Type.UVar (pos, uv)) t) t'
                    end
                )
              | checkSub annEnv (t as Type.OVar (_, ov)) (t' as Type.OVar (_, ov')) =
                if TypeVars.ovInScope ov
                then if TypeVars.ovInScope ov'
                     then if TypeVars.ovEq (ov, ov')
                          then ()
                          else raise TypeError (TypeMismatch (t, t'))
                     else raise TypeError (OvOutOfScope (TypeVars.ovName ov))
                else raise TypeError (OvOutOfScope (TypeVars.ovName ov'))
              | checkSub annEnv (Type.Arrow (_, arr)) (Type.Arrow (_, arr')) =
                 ( checkSub annEnv (#domain arr') (#domain arr)
                 ; checkSub annEnv (#codomain arr) (#codomain arr') )
              | checkSub annEnv (t as Type.Prim (_, p)) (t' as Type.Prim (_, p')) =
                if p = p' then () else raise TypeError (TypeMismatch (t, t'))
              | checkSub annEnv t t' = raise TypeError (TypeMismatch (t, t'))

            fun check annEnv env =
                fn Cst.Fn (pos, param, maybeAnn, body) =>
                    let val (domain, annEnv) =
                            case maybeAnn
                            of SOME ann => let val (t, annEnv) = hydrateBinder tenv pos annEnv ann
                                           in if Type.isWellFormedType annEnv t
                                              then (t, annEnv)
                                              else raise TypeError (MalformedType t)
                                           end
                             | NONE =>
                                (Type.UVar (pos, TypeVars.pushUv tenv (Name.fresh ())), annEnv)
                        val codomain = Type.UVar (pos, TypeVars.pushUv tenv (Name.fresh ()))
                    in withMarker tenv (fn () =>
                           let val env = ValTypeCtx.insert env param domain
                               val body' = checkAs annEnv env codomain body
                           in ( Cst.Fn (pos, param, SOME domain, body')
                              , Type.Arrow (pos, {domain, codomain}) )
                           end
                       )
                    end
                 | Cst.App (pos, {callee, arg}) =>
                    let val (callee', {domain, codomain}) = coerceCallee (check annEnv env callee)
                        val arg' = checkAs annEnv env domain arg
                    in (Cst.App (pos, {callee = callee', arg = arg'}), codomain)
                    end
                 | Cst.Ann (pos, expr, ann) =>
                    let val t = hydrate annEnv ann
                    in if Type.isWellFormedType annEnv t
                       then let val expr' = checkAs annEnv env t expr
                            in (Cst.Ann (pos, expr', ann), t)
                            end
                       else raise TypeError (MalformedType t)
                    end
                 | Cst.Use (pos, name) => (case ValTypeCtx.find env name
                                           of SOME t => (Cst.Use (pos, name), t)
                                            | NONE => raise TypeError (Unbound name))
                 | Cst.Const (pos, c) => let val (c, t) = checkConst pos c
                                         in (Cst.Const (pos, c), t)
                                         end

            and checkAs annEnv env (Type.ForAll (pos, param, t)) expr =
                withOv tenv param (fn ov =>
                    checkAs annEnv env (Type.substitute (param, Type.OVar (pos, ov)) t) expr
                )
              | checkAs annEnv env (Type.Arrow (_, {domain, codomain}))
                                   (Cst.Fn (pos, param, maybeAnn, body)) =
                let val (domain, annEnv) =
                        case maybeAnn
                        of SOME ann => let val (t, annEnv) = hydrateBinder tenv pos annEnv ann
                                       in if Type.isWellFormedType annEnv t
                                          then ( checkSub annEnv domain t
                                               ; (t, annEnv) )
                                          else raise TypeError (MalformedType t)
                                       end
                         | NONE => (domain, annEnv)
                in withMarker tenv (fn () =>
                       let val env = ValTypeCtx.insert env param domain
                           val body' = checkAs annEnv env codomain body
                       in Cst.Fn (pos, param, SOME domain, body')
                       end
                   )
                end
              | checkAs annEnv env t expr =
                let val (expr', t') = check annEnv env expr
                in checkSub annEnv t' t
                 ; expr'
                end

            and coerceCallee (callee, t) =
                (case t
                 of Type.ForAll (pos, param, t') =>
                     let val uv = TypeVars.pushUv tenv (Name.fresh ())
                     in coerceCallee (callee, Type.substitute (param, Type.UVar (pos, uv)) t')
                     end
                  | Type.UVar (pos, uv) =>
                     (case TypeVars.uvGet uv
                      of Either.Left uv =>
                          let val (duv, cuv) = articulate tenv uv
                          in (callee, { domain = Type.UVar (pos, duv)
                                      , codomain = Type.UVar (pos, cuv) })
                          end
                      | Either.Right t' => coerceCallee (callee, t'))
                  | Type.Arrow (_, arr) => (callee, arr)
                  | _ => raise TypeError (Uncallable (callee, t)))

            fun checkStmt annEnv env =
                fn Cst.Def (pos, name, _, expr) =>
                    let val t = valOf (ValTypeCtx.find env name)
                        val expr' = checkAs annEnv env t expr
                    in Cst.Def (pos, name, SOME t, expr')
                    end

            fun checkStmts annEnv env stmts =
                let val names = Vector.map (fn Cst.Def (_, name, _, _) => name) stmts
                    val anns = Vector.map (fn Cst.Def (pos, _, maybeAnn, _) =>
                                               case maybeAnn
                                               of SOME ann => ann
                                                | NONE => Type.UseT (pos, Name.fresh ()))
                                          stmts
                    val (ts, annEnv) = hydrateBinders tenv annEnv anns
                    val env = Vector.foldli (fn (i, name, env) =>
                                                 let val t = Vector.sub (ts, i)
                                                 in ValTypeCtx.insert env name t
                                                 end)
                                            env names
                in Vector.app (fn t => if Type.isWellFormedType annEnv t
                                       then ()
                                       else raise TypeError (MalformedType t))
                              ts
                 ; Vector.map (checkStmt annEnv env) stmts
                end                             
        in Either.Right (checkStmts ValTypeCtx.empty ValTypeCtx.empty program)
           handle TypeError err => Either.Left err
        end
end
