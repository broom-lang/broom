(* FIXME: Cannot use union by rank (unless the `uv`:s' scopes are identical)! *)
(* TODO: Lift out the `ref` in `env`, making this immutable. *)

signature TYPE_VARS = sig
    eqtype ov   (* Opaque variable *)
    type 't uv  (* Unification variable *)
    type 't env (* Type variable environment *)

    exception OvOutOfScope of Name.t
    exception UvOutOfScope of Name.t
    exception UvsOutOfScope of Name.t * Name.t
    exception NoUvMark of Name.t

    val newEnv: unit -> 't env
    val splitEnvBefore: 't env -> 't uv -> 't env

    val uvName: 't uv -> Name.t
    val uvGet: 't uv -> ('t uv, 't) Either.t
    val uvEq: 't uv -> 't uv -> bool
    val uvSet: 't uv -> 't -> unit

    val pushOv: 't env -> Name.t -> ov
    val pushOv': 't env -> ov -> unit
    val popOv: 't env -> ov -> unit

    val pushUv: 't env -> Name.t -> 't uv
    val pushParUvs: 't env -> Name.t vector -> 't uv vector
    val pushScopedUv: 't env -> Name.t -> 't uv
    val insertUvBefore: 't env -> 't uv -> Name.t -> 't uv
    val popScopedUv: 't env -> 't uv -> unit

    val ovInScope: 't env -> ov -> bool
    val uvInScope: 't env -> 't uv -> bool
    val compareUvScopes: 't env -> 't uv -> 't uv -> order

    structure ValEnv: sig
        type 't env

        val empty: 't env
        val find: 't env -> Name.t -> 't option
        val insert: 't env -> Name.t -> 't -> 't env
    end
end

structure ValTypeCtx = struct
    type 't env = 't NameSortedMap.map

    val empty = NameSortedMap.empty

    (* O(log n) *)
    fun find env name = NameSortedMap.find (env, name)

    (* O(log n)*)
    fun insert env name v = NameSortedMap.insert (env, name, v)
end

structure TypeVars :> TYPE_VARS = struct
    type ov = Name.t
    type 't uv = {typ: 't option ref, name: Name.t} UnionFind.t
    datatype 't binding = Opaque of ov
                        | Unif of 't uv
                        | Marker of 't uv
                        | Par of 't binding vector
    type 't env = 't binding list ref

    exception OvOutOfScope of Name.t
    exception UvOutOfScope of Name.t
    exception UvsOutOfScope of Name.t * Name.t
    exception NoUvMark of Name.t

    (* O(1) *)
    fun newEnv () = ref []

    val uvFind: 't uv -> 't uv = UnionFind.find
    fun uvGet uv = let val uv = uvFind uv
                   in case !(#typ (UnionFind.content uv))
                      of SOME t => Either.Right t
                       | NONE => Either.Left uv
                   end
    fun uvName uv = #name (UnionFind.content (uvFind uv))
    fun uvEq uv uv' = UnionFind.eq (uvFind uv) (uvFind uv')
    fun uvSet uv t = #typ (UnionFind.content (uvFind uv)) := SOME t

    (* O(1) *)
    fun bindingOfOv ov = fn Opaque ov' => ov' = ov
                          | Unif _ => false
                          | Marker _ => false
                          | Par bs => isSome (Vector.find (bindingOfOv ov) bs)
    fun bindingOfUv uv = fn Opaque _ => false
                          | Unif uv' => UnionFind.eq uv' uv
                          | Marker _ => false
                          | Par bs => isSome (Vector.find (bindingOfUv uv) bs)
    fun markerOfUv uv = fn Opaque _ => false
                         | Unif _ => false
                         | Marker uv' => UnionFind.eq uv' uv
                         | Par bs => isSome (Vector.find (bindingOfUv uv) bs)
    fun freshUv name = UnionFind.new {typ = ref NONE, name = name}

    (* O(n) *)
    fun splitEnvBefore env uv =
        let val rec split = fn [] => raise UvOutOfScope (uvName uv)
                             | b :: bs => if bindingOfUv uv b
                                          then (bs, [b])
                                          else let val (bottom, top) = split bs
                                               in (bottom, b :: top)
                                               end
            val (bottom, top) = split (!env)
        in env := bottom
         ; ref top
        end

    (* O(1) *)
    fun pushOv env name = (env := (Opaque name :: !env); name)
    fun pushOv' env ov = env := (Opaque ov :: !env)
    fun pushUv env name = let val uv = freshUv name
                          in env := (Unif uv :: !env)
                           ; uv
                          end
    fun pushParUvs env names = let val uvs = Vector.map freshUv names
                               in env := (Par (Vector.map Unif uvs) :: !env)
                                ; uvs
                               end
    fun pushScopedUv env name = let val uv = freshUv name
                                in env := (Unif uv :: Marker uv :: !env)
                                 ; uv
                                end

    (* O(n) *)
    fun insertUvBefore env uv name =
        let val uv' = freshUv name
            val rec insert = fn [] => raise UvOutOfScope (uvName uv)
                              | b :: bs => b :: (if bindingOfUv uv b
                                                 then Unif uv' :: bs
                                                 else insert bs)
        in env := insert (!env)
         ; uv'
        end

    (* O(n) *)
    fun popUntilAnd pred = fn [] => NONE
                            | x :: xs => if pred x
                                         then SOME xs
                                         else popUntilAnd pred xs
    fun popOv env ov = case popUntilAnd (bindingOfOv ov) (!env)
                        of SOME bindings => env := bindings
                         | NONE => raise OvOutOfScope ov
    fun popScopedUv env uv = case popUntilAnd (markerOfUv uv) (!env)
                             of SOME bindings => env := bindings
                              | NONE => raise UvOutOfScope (uvName uv)

    (* O(n) *)
    fun bindingInScope bindings pred = isSome (List.find pred bindings)
    fun ovInScope env ov = bindingInScope (!env) (bindingOfOv ov)
    fun uvInScope env uv = bindingInScope (!env) (bindingOfUv uv)

    exception Done of order

    (* O(n) and probably buggy for nested `Par`:s (which shouldn't happen anyway but hey...) *)
    fun compareUvScopes env uv uv' =
        let fun comparisonStep inPar (b, state) =
                case b
                of Opaque _ => state
                 | Unif uv'' => (case state
                                 of NONE => if UnionFind.eq uv'' uv
                                            then SOME (GREATER, inPar)
                                            else if UnionFind.eq uv'' uv'
                                            then SOME (LESS, inPar)
                                            else state
                                  | SOME (ord, samePar) =>
                                      let val outerUv = case ord
                                                        of GREATER => uv'
                                                         | LESS => uv
                                                         | EQUAL => raise Fail "unreachable"
                                      in if UnionFind.eq uv'' outerUv
                                         then raise Done (if samePar then EQUAL else ord)
                                         else state
                                      end)
                 | Marker _ => state
                 | Par bs => (case Vector.foldl (comparisonStep true) state bs
                              of SOME (ord, _) => SOME (ord, false)
                               | NONE => NONE)
        in (case List.foldl (comparisonStep false) NONE (!env)
            of SOME (GREATER, _) => raise UvOutOfScope (uvName uv')
             | SOME (LESS, _) => raise UvOutOfScope (uvName uv)
             | SOME (EQUAL, _) => raise Fail "unreachable"
             | NONE => raise UvsOutOfScope (uvName uv, uvName uv'))
           handle Done ord => ord
        end

    structure ValEnv = ValTypeCtx
end

structure FancyTypeVars :> sig
    exception Reset of Name.t

    type ov
    val ovName: ov -> Name.t

    type 't uv
    val uvName: 't uv -> Name.t
    val uvGet: 't uv -> ('t uv, 't) Either.t
    val uvSet: 't uv -> 't -> unit
    val uvMerge: 't uv -> 't uv -> unit

    type 't env
    val newEnv: unit -> 't env

    val pushOv: 't env -> Name.t -> 't env * ov
    val pushUv: 't env -> Name.t -> 't env * 't uv
end = struct
    structure Level :> sig
        structure Digit: sig
            type t

            val maxValue: int
            val fromInt: int -> t
        end

        type id
        val empty: id
        val push: id -> Digit.t -> id
        val compare: id * id -> order
    end = struct
        structure Digit = struct
            type t = Word8.word

            val maxValue = Word.toInt (Word.<< (Word.fromInt 1, Word.fromInt Word8.wordSize)) - 1
            fun fromInt n = if n <= maxValue then Word8.fromInt n else raise Overflow
        end

        type id = Word8.word vector

        val empty = Vector.fromList []

        fun push id d = VectorExt.push (id, d)

        fun compare (bytes, bytes') =
            let val len = Vector.length bytes
                val len' = Vector.length bytes'
                fun loop i ord =
                    let val byte = if i < len then SOME (Vector.sub (bytes, i)) else NONE
                        val byte' = if i < len' then SOME (Vector.sub (bytes', i)) else NONE
                    in case (byte, byte')
                       of (NONE, NONE) => ord
                        | _ => (case Word8.compare ( getOpt (byte, Word8.fromInt 0)
                                                   , getOpt (byte', Word8.fromInt 0) )
                                of EQUAL => loop (i + 1) EQUAL
                                 | ord => ord)
                    end
            in loop 0 EQUAL
            end
    end

    exception Reset of Name.t

    type var_descr = {name: Name.t, levelId: Level.id, inScope: bool ref}

    type ov = var_descr

    fun ovName (ov: ov) = #name ov

    datatype 't uv_link = Root of {descr: var_descr, typ: 't option ref}
                        | Link of 't uv
    withtype 't uv = 't uv_link ref

    fun uvFind uv = case !uv
                    of Root _ => uv
                     | Link uv' => let val res = uvFind uv'
                                   in uv := Link res (* path compression *)
                                    ; res
                                   end

    fun uvName uv = case !(uvFind uv)
                    of Root {descr = {name, ...}, ...} => name
                     | Link _ => raise Fail "unreachable"

    fun uvGet uv = let val uv = uvFind uv
                   in case !uv
                      of Root {typ, ...} => (case !typ
                                             of SOME t => Either.Right t
                                              | NONE => Either.Left uv)
                       | Link _ => raise Fail "unreachable"
                   end

    fun uvSet uv t = let val uv = uvFind uv
                     in case !uv
                        of Root {descr = {name, ...}, typ} => typ := SOME t
                         | Link _ => raise Fail "unreachable"
                     end

    fun uvMerge uv uv' = let val uv = uvFind uv
                             val uv' = uvFind uv'
                         in case (!uv, !uv')
                            of ( Root {descr = {levelId = l, ...}, ...}
                               , Root {descr = {levelId = l', ...}, ...} ) =>
                                (case Level.compare (l, l')
                                 of LESS => uv' := Link uv
                                  | GREATER => uv := Link uv'
                                  | EQUAL => uv' := Link uv) (* OPTIMIZE: Union by rank here? *)
                            | _ => raise Fail "unreachable"
                         end

    datatype 't var = Ov of ov
                    | Uv of 't uv
    datatype 't scope = Single of 't var
                      | Par of 't var vector

    datatype 't env_node = Env of 't env
                         | Scope of 't scope
    withtype 't env = 't env_node vector

    fun newEnv () = Vector.fromList [Env (Vector.fromList [])]

    fun nodePushScope scopeFromLevelId envNode prefix =
        case envNode
        of Env env => envPushScope scopeFromLevelId env prefix
         | Scope _ => let val id = Level.push prefix (Level.Digit.fromInt 1)
                          val scope = scopeFromLevelId id
                      in (Vector.fromList [envNode, Scope scope], scope)
                      end

    and envPushScope scopeFromLevelId env prefix =
        let val i = Vector.length env
            val id = Level.push prefix (Level.Digit.fromInt i)
            val (lastNode, scope) =
                case Int.compare (i, Level.Digit.maxValue)
                of LESS | EQUAL => let val scope = scopeFromLevelId id
                                   in (Scope scope, scope)
                                   end
                 | GREATER =>
                    let val (env, scope) = nodePushScope scopeFromLevelId (Vector.sub (env, i)) id
                    in (Env env, scope)
                    end
        in (VectorExt.push (env, lastNode), scope)
        end

    fun pushOv env name =
        case envPushScope (fn levelId => Single (Ov {name, levelId, inScope = ref true}))
                          env Level.empty
        of (env, Single (Ov ov)) => (env, ov)
         | _ => raise Fail "unreachable"

    fun pushUv env name =
        case envPushScope (fn levelId =>
                               Single (Uv (ref (Root { descr = {name, levelId, inScope = ref true}
                                                     , typ = ref NONE }))))
                          env Level.empty
        of (env, Single (Uv uv)) => (env, uv)
         | _ => raise Fail "unreachable"
end
