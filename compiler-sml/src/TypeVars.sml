signature TYPE_VARS = sig
    type ov     (* Opaque variable *)
    type 't uv  (* Unification variable *)
    type 't env (* Type variable environment *)

    exception OvOutOfScope of Name.t
    exception UvOutOfScope of Name.t
    exception UvsOutOfScope of Name.t * Name.t
    exception NoUvMark of Name.t

    val newEnv: unit -> 't env

    val uvFind: 't uv -> 't uv
    val uvEq: 't uv -> 't uv -> bool

    val pushOv: 't env -> Name.t -> ov
    val pushOv': 't env -> ov -> unit
    val popOv: 't env -> ov -> unit

    val pushUv: 't env -> Name.t -> 't uv
    val pushScopedUv: 't env -> Name.t -> 't uv
    val insertUvBefore: 't env -> 't uv -> Name.t -> 't uv
    val popScopedUv: 't env -> 't uv -> unit

    val ovInScope: 't env -> ov -> bool
    val uvInScope: 't env -> 't uv -> bool
    val compareUvScopes: 't env -> 't uv -> 't uv -> order
end

structure TypeVars :> TYPE_VARS = struct
    type ov = Name.t
    type 't uv = {typ: 't option ref, name: Name.t} UnionFind.t
    datatype 't binding = Opaque of ov
                        | Unif of 't uv
                        | Marker of 't uv
    type 't env = 't binding list ref

    exception OvOutOfScope of Name.t
    exception UvOutOfScope of Name.t
    exception UvsOutOfScope of Name.t * Name.t
    exception NoUvMark of Name.t

    fun newEnv () = ref []

    (* O(1) *)
    val uvFind = UnionFind.find
    fun uvName uv = #name (UnionFind.content (uvFind uv))
    fun uvEq uv uv' = UnionFind.eq (uvFind uv) (uvFind uv')

    (* O(1) *)
    fun bindingOfOv ov = fn Opaque ov' => ov' = ov
                          | Unif _ => false
                          | Marker _ => false
    fun bindingOfUv uv = fn Opaque _ => false
                          | Unif uv' => UnionFind.eq uv' uv
                          | Marker _ => false
    fun markerOfUv uv = fn Opaque _ => false
                         | Unif _ => false
                         | Marker uv' => UnionFind.eq uv' uv
    fun freshUv name = UnionFind.new {typ = ref NONE, name = name}

    (* O(1) *)
    fun pushOv env name = (env := (Opaque name :: !env); name)
    fun pushOv' env ov = env := (Opaque ov :: !env)
    fun pushUv env name = let val uv = freshUv name
                          in env := (Unif uv :: !env)
                           ; uv
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

    (* O(n) *)
    fun compareUvScopes env uv uv' =
        let fun ensureOuter env uv = if bindingInScope env (bindingOfUv uv)
                                     then ()
                                     else raise UvOutOfScope (uvName uv)
            val rec findInner = fn [] => raise UvsOutOfScope (uvName uv, uvName uv')
                                 | Opaque _ :: env' => findInner env'
                                 | Unif uv'' :: env' =>
                                    if UnionFind.eq uv'' uv
                                    then (ensureOuter env' uv'; GREATER)
                                    else if UnionFind.eq uv'' uv'
                                    then (ensureOuter env' uv; LESS)
                                    else findInner env'
                                 | Marker _ :: env' => findInner env'
        in findInner (!env)
        end
end
