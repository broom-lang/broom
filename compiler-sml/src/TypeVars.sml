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

    val uvFind: 't uv -> 't uv
    val uvEq: 't uv -> 't uv -> bool

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

        val findVal: 't env -> Name.t -> 't option
        val insertVal: 't env -> Name.t -> 't -> 't env
    end
end

structure ValTypeCtx = struct
    type 't env = 't NameSortedMap.map

    (* O(log n) *)
    fun findVal env name = NameSortedMap.find (env, name)

    (* O(log n)*)
    fun insertVal env name v = NameSortedMap.insert (env, name, v)
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

    val uvFind = UnionFind.find
    fun uvName uv = #name (UnionFind.content (uvFind uv))
    fun uvEq uv uv' = UnionFind.eq (uvFind uv) (uvFind uv')

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
