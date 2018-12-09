structure Typecheck :> sig
    datatype error = UvOutOfScope of Name.t
                   | OvOutOfScope of Name.t
                   | Unbound of Name.t
                   | UnboundType of Name.t
                   | Occurs of Type.t TypeVars.uv * Type.t
                   | Uncallable of SemiFAst.Term.expr * Type.t
                   | TypeMismatch of Type.t * Type.t
                   | MalformedType of Type.t

    val errorToString: error -> string

    val typecheck: Cst.stmt vector -> (error, SemiFAst.Term.stmt vector) Either.t
end = struct
    structure FTerm = SemiFAst.Term

    val articulate2 = TypeCtx.articulate2
    val withOv = TypeCtx.withOv
    val withMarker = TypeCtx.withMarker
    val withValType = TypeCtx.withValType
    val withValTypes = TypeCtx.withValTypes
    val withSrcType = TypeCtx.withSrcType
    val withSrcTypes = TypeCtx.withSrcTypes

    datatype error = UvOutOfScope of Name.t
                   | OvOutOfScope of Name.t
                   | Unbound of Name.t
                   | UnboundType of Name.t
                   | Occurs of Type.t TypeVars.uv * Type.t
                   | Uncallable of FTerm.expr * Type.t
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
                            "Uncallable: " ^ FTerm.exprToString expr ^ ": " ^ Type.toString t
                         | TypeMismatch (t, t') =>
                            "TypeMismatch: " ^ Type.toString t ^ " " ^ Type.toString t'
                         | MalformedType t => "MalformedType: " ^ Type.toString t

    datatype lattice_y = Sub | Super

    val flipY = fn Sub => Super
                 | Super => Sub

    fun annFreeVars tenv =
        fn Type.ForAll (pos, param, body) =>
            withSrcType tenv param (Type.UseT (pos, param)) (fn () =>
                annFreeVars tenv body
            )
         | Type.UseT (_, name) => if isSome (TypeCtx.findSrcType tenv name)
                                  then NameSortedSet.empty
                                  else NameSortedSet.fromList [name]
         | Type.OVar _ => NameSortedSet.empty
         | Type.UVar _ => NameSortedSet.empty
         | Type.Arrow (_, {domain, codomain}) =>
            NameSortedSet.union (annFreeVars tenv domain, annFreeVars tenv codomain)
         | Type.Prim _ => NameSortedSet.empty

    fun hydrate tenv ann =
        let val rec hydr =
                fn Type.ForAll (pos, param, t) =>
                    Type.ForAll ( pos, param
                                , withSrcType tenv param (Type.UseT (pos, param)) (fn () =>
                                      hydr t
                                  ) )
                 | Type.UseT (_, name) => (case TypeCtx.findSrcType tenv name
                                           of SOME t => t
                                            | NONE => raise TypeError (UnboundType name))
                 | t as Type.OVar _ => t
                 | t as Type.UVar _ => t
                 | Type.Arrow (pos, {domain, codomain}) =>
                    Type.Arrow (pos, {domain = hydr domain, codomain = hydr codomain})
                 | t as Type.Prim (pos, p) => t
            val t = hydr ann
        in if Type.isWellFormedType tenv t
           then t
           else raise TypeError (MalformedType t)
        end
    
    fun annsSrcTypes tenv anns =
        let val fvs = Vector.foldl (fn (ann, fvs) =>
                                        NameSortedSet.union (annFreeVars tenv ann, fvs))
                                   NameSortedSet.empty anns
            val fvs = Vector.fromList (NameSortedSet.toList fvs)
            val uvs = TypeCtx.pushUvs tenv fvs
            val pos = Type.pos (Vector.sub (anns, 0))
        in Vector.mapi (fn (i, fv) => (fv, Type.UVar (pos, Vector.sub (uvs, i)))) fvs
        end
    
    fun checkConst pos = fn c as Const.Int _ => (c, Type.Prim (pos, Type.Int))

    fun typecheck program =
        let val tenv = TypeCtx.new ()

            fun assignForSome pos param y uv t =
                case y
                of Sub =>
                   withOv tenv param (fn ov =>
                       assign y uv (Type.substitute (param, Type.OVar (pos, ov)) t)
                   )
                 | Super =>
                   withMarker tenv (fn () =>
                       let val uv' = TypeCtx.pushUv tenv (Name.fresh ())
                       in assign y uv (Type.substitute (param, Type.UVar (pos, uv')) t)
                       end
                   )

            and assign y uv t =
                let fun doassign uv =
                        fn Type.ForAll (pos, param, t') => assignForSome pos param y uv t'
                         | t as Type.UseT _ => raise Fail "unreachable"
                         | t as Type.OVar _ => TypeVars.uvSet uv t
                         | Type.UVar (pos, uv') => (case TypeVars.uvGet uv'
                                                    of Either.Left uv' => TypeVars.uvMerge uv uv'
                                                     | Either.Right t => doassign uv t)
                         | Type.Arrow (_, {domain, codomain}) =>
                            let val (duv, cuv) = articulate2 tenv uv
                            in assign (flipY y) duv domain
                             ; assign y cuv codomain
                            end
                         | t as Type.Prim _ => TypeVars.uvSet uv t
                in if TypeVars.uvInScope uv
                   then if Type.occurs uv t
                        then raise TypeError (Occurs (uv, t))
                        else doassign uv t
                   else raise TypeError (UvOutOfScope (TypeVars.uvName uv))
                end

            (* TODO: Produce coercion code: *)
            fun checkSub (Type.UVar (_, uv)) (Type.UVar (_, uv')) =
                (case (TypeVars.uvGet uv, TypeVars.uvGet uv')
                 of (Either.Left uv, Either.Left uv') =>
                     if TypeVars.uvInScope uv
                     then if TypeVars.uvInScope uv'
                          then if TypeVars.uvEq (uv, uv') then () else TypeVars.uvMerge uv uv'
                          else raise TypeError (UvOutOfScope (TypeVars.uvName uv'))
                     else raise TypeError (UvOutOfScope (TypeVars.uvName uv))
                  | (Either.Left uv, Either.Right t') => assign Sub uv t'
                  | (Either.Right t, Either.Left uv') => assign Super uv' t
                  | (Either.Right t, Either.Right t') => checkSub t t')
              | checkSub (Type.UVar (_, uv)) t' =
                (case TypeVars.uvGet uv
                 of Either.Left uv => assign Sub uv t'
                  | Either.Right t => checkSub t t')
              | checkSub t (Type.UVar (_, uv')) =
                (case TypeVars.uvGet uv'
                 of Either.Left uv' => assign Super uv' t
                  | Either.Right t' => checkSub t t')
              | checkSub t (Type.ForAll (pos, param, t')) =
                withOv tenv param (fn ov =>
                    checkSub t (Type.substitute (param, Type.OVar (pos, ov)) t')
                )
              | checkSub (Type.ForAll (pos, ov, t)) t' =
                withMarker tenv (fn () =>
                    let val uv = TypeCtx.pushUv tenv (Name.fresh ())
                    in checkSub (Type.substitute (ov, Type.UVar (pos, uv)) t) t'
                    end
                )
              | checkSub (t as Type.OVar (_, ov)) (t' as Type.OVar (_, ov')) =
                if TypeVars.ovInScope ov
                then if TypeVars.ovInScope ov'
                     then if TypeVars.ovEq (ov, ov')
                          then ()
                          else raise TypeError (TypeMismatch (t, t'))
                     else raise TypeError (OvOutOfScope (TypeVars.ovName ov))
                else raise TypeError (OvOutOfScope (TypeVars.ovName ov'))
              | checkSub (Type.Arrow (_, arr)) (Type.Arrow (_, arr')) =
                ( checkSub (#domain arr') (#domain arr)
                ; checkSub (#codomain arr) (#codomain arr') )
              | checkSub (t as Type.Prim (_, p)) (t' as Type.Prim (_, p')) =
                if p = p'
                then ()
                else raise TypeError (TypeMismatch (t, t'))
              | checkSub t t' =
                raise TypeError (TypeMismatch (t, t'))

            fun check (Cst.Fn (pos, param, maybeAnn, body)) =
                let val ann = case maybeAnn
                              of SOME ann => ann
                               | NONE => Type.UseT (pos, Name.fresh ())
                    val ext = annsSrcTypes tenv (Vector.fromList [ann])
                in withSrcTypes tenv ext (fn () =>
                       let val domain = hydrate tenv ann
                           val codomain = Type.UVar (pos, TypeCtx.pushUv tenv (Name.fresh ()))
                       in withValType tenv param domain (fn () =>
                              ( FTerm.Fn (pos, {name = param, typ = domain}, checkAs codomain body)
                              , Type.Arrow (pos, {domain, codomain}) )
                          )
                       end
                   )
                end
              | check (Cst.App (pos, {callee, arg})) =
                let val (callee', {domain, codomain}) = coerceCallee (check callee)
                    val arg' = checkAs domain arg
                in (FTerm.App (pos, {callee = callee', arg = arg'}), codomain)
                end
              | check (Cst.Ann (pos, expr, ann)) =
                let val t = hydrate tenv ann
                in (checkAs t expr, t)
                end
              | check (Cst.Use (pos, name)) =
                (case TypeCtx.findValType tenv name
                 of SOME typ => (FTerm.Use (pos, {name, typ}), typ)
                  | NONE => raise TypeError (Unbound name))
              | check (Cst.Const (pos, c)) =
                let val (c, t) = checkConst pos c
                in (FTerm.Const (pos, c), t)
                end

            and checkAs (Type.ForAll (pos, param, t)) expr =
                withOv tenv param (fn ov =>
                    checkAs (Type.substitute (param, Type.OVar (pos, ov)) t) expr
                )
              | checkAs (Type.Arrow (_, {domain, codomain}))
                            (Cst.Fn (pos, param, maybeAnn, body)) =
                let val ann = case maybeAnn
                              of SOME ann => ann
                               | NONE => Type.UseT (pos, Name.fresh ())
                    val ext = annsSrcTypes tenv (Vector.fromList [ann])
                in withSrcTypes tenv ext (fn () =>
                       let val domain' = hydrate tenv ann
                           do checkSub domain domain'
                           val domain = domain'
                           val codomain = Type.UVar (pos, TypeCtx.pushUv tenv (Name.fresh ()))
                       in withValType tenv param domain (fn () =>
                              FTerm.Fn (pos, {name = param, typ = domain}, checkAs codomain body)
                          )
                       end
                   )
                end
              | checkAs t expr =
                let val (expr', t') = check expr
                in checkSub t' t
                 ; expr'
                end

            and coerceCallee (callee, t) =
                (case t
                 of Type.ForAll (pos, param, t') =>
                     let val uv = TypeCtx.pushUv tenv (Name.fresh ())
                     in coerceCallee (callee, Type.substitute (param, Type.UVar (pos, uv)) t')
                     end
                  | Type.UVar (pos, uv) =>
                     (case TypeVars.uvGet uv
                      of Either.Left uv =>
                          let val (duv, cuv) = articulate2 tenv uv
                          in (callee, { domain = Type.UVar (pos, duv)
                                      , codomain = Type.UVar (pos, cuv) })
                          end
                      | Either.Right t' => coerceCallee (callee, t'))
                  | Type.Arrow (_, arr) => (callee, arr)
                  | _ => raise TypeError (Uncallable (callee, t)))

            val checkStmt =
                fn Cst.Def (pos, name, _, expr) =>
                    let val typ = valOf (TypeCtx.findValType tenv name)
                        val expr' = checkAs typ expr
                    in FTerm.Def (pos, {name, typ}, expr')
                    end

            fun checkStmts stmts =
                let val names = Vector.map (fn Cst.Def (_, name, _, _) => name) stmts
                    val anns = Vector.map (fn Cst.Def (pos, _, maybeAnn, _) =>
                                               case maybeAnn
                                               of SOME ann => ann
                                                | NONE => Type.UseT (pos, Name.fresh ()))
                                          stmts
                    val ext = annsSrcTypes tenv anns
                in withSrcTypes tenv ext (fn () =>
                       let val ts = Vector.map (hydrate tenv) anns
                           val vext = Vector.mapi (fn (i, name) => (name, Vector.sub (ts, i))) names
                       in withValTypes tenv vext (fn () =>
                              Vector.map checkStmt stmts
                          )
                       end
                   )
                end                         
        in Either.Right (checkStmts program)
           handle TypeError err => Either.Left err
        end
end
