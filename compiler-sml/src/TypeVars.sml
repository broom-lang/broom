signature TYPE_VARS = sig
    exception Reset of Name.t

    type ov
    val ovEq: ov * ov -> bool
    val ovName: ov -> Name.t

    type 't uv
    val uvEq: 't uv * 't uv -> bool
    val uvName: 't uv -> Name.t
    val uvGet: 't uv -> ('t uv, 't) Either.t
    val uvSet: 't uv -> 't -> unit
    val uvMerge: 't uv -> 't uv -> unit

    type marker

    type 't env
    val newEnv: unit -> 't env

    val pushOv: 't env -> ov -> unit
    val pushUv: 't env -> Name.t -> 't uv
    val pushUvs: 't env -> Name.t vector -> 't uv vector
    val pushMarker: 't env -> marker
    val pushScopedUv: 't env -> Name.t -> 't uv * marker
    val insertUvBefore: 't env -> 't uv -> Name.t -> 't uv

    val popOv: 't env -> ov -> unit
    val popUv: 't env -> 't uv -> unit
    val popMarker: 't env -> marker -> unit

    val ovInScope: 't env -> ov -> bool
    val uvInScope: 't env -> 't uv -> bool
end

signature VAL_TYPE_CTX = sig
    type 't env

    val empty: 't env
    val find: 't env -> Name.t -> 't option
    val insert: 't env -> Name.t -> 't -> 't env
end

structure ValTypeCtx :> VAL_TYPE_CTX = struct
    type 't env = 't NameSortedMap.map

    val empty = NameSortedMap.empty

    (* O(log n) *)
    fun find env name = NameSortedMap.find (env, name)

    (* O(log n)*)
    fun insert env name v = NameSortedMap.insert (env, name, v)
end

structure Version :> sig
    structure Digit: sig
        type t

        val maxValue: int
        val fromInt: int -> t
        val toInt: t -> int
    end

    type id
    val empty: id
    val push: id -> Digit.t -> id
    val pred: id -> id
    val length: id -> int
    val digit: id -> int -> Digit.t
    val compare: id * id -> order
end = struct
    structure Digit = struct
        type t = Word8.word

        val maxValue = Word.toInt (Word.<< (Word.fromInt 1, Word.fromInt Word8.wordSize)) - 1
        fun fromInt n = if n <= maxValue then Word8.fromInt n else raise Overflow
        val toInt = Word8.toInt
    end

    type id = Word8.word vector

    val empty = Vector.fromList []

    fun push id d = VectorExt.push (id, d)

    val length = Vector.length

    fun pred id = let val i = length id - 1
                      val n = Digit.toInt (Vector.sub (id, i))
                  in Vector.update (id, i, Word8.fromInt (n - 1))
                  end

    fun digit id i = Vector.sub (id, i)

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

structure TypeVars :> TYPE_VARS = struct
    exception Reset of Name.t

    type var_descr = {name: Name.t, version: Version.id, inScope: bool ref}

    type ov = var_descr

    fun ovEq (ov: ov, ov': ov) = #inScope ov = #inScope ov' (* TODO: is this correct/well-named? *)

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

    fun uvEq (uv, uv') = uvFind uv = uvFind uv'

    fun uvRoot uv = case !(uvFind uv)
                    of Root root => root
                     | Link _ => raise Fail "unreachable"

    fun uvName uv = #name (#descr (uvRoot uv))

    fun uvGet uv = let val uv = uvFind uv
                   in case !uv
                      of Root {typ, ...} => (case !typ
                                             of SOME t => Either.Right t
                                              | NONE => Either.Left uv)
                       | Link _ => raise Fail "unreachable"
                   end

    fun uvSet uv t = #typ (uvRoot uv) := SOME t

    fun uvMerge uv uv' = let val uv = uvFind uv
                             val uv' = uvFind uv'
                         in case (!uv, !uv')
                            of ( Root {descr = {version = l, ...}, ...}
                               , Root {descr = {version = l', ...}, ...} ) =>
                                (case Version.compare (l, l')
                                 of LESS => uv' := Link uv
                                  | GREATER => uv := Link uv'
                                  | EQUAL => uv' := Link uv) (* OPTIMIZE: Union by rank here? *)
                            | _ => raise Fail "unreachable"
                         end

    type marker = Version.id

    datatype 't var = Ov of ov
                    | Uv of 't uv

    datatype 't binding_node = Bindings of 't bindings
                             | Scope of 't var vector
    withtype 't bindings = 't binding_node vector

    type 't env = 't bindings ref

    fun newEnv () = ref (Vector.fromList [Bindings (Vector.fromList [])])

    fun nodePushScope scopeFromVersion envNode prefix =
        case envNode
        of Bindings bindings => bindingsPushScope scopeFromVersion bindings prefix
         | Scope _ => let val id = Version.push prefix (Version.Digit.fromInt 1)
                      in Vector.fromList [envNode, Scope (scopeFromVersion id)]
                      end

    and bindingsPushScope scopeFromVersion bindings prefix =
        let val i = Vector.length bindings
            val id = Version.push prefix (Version.Digit.fromInt i)
            val lastNode =
                case Int.compare (i, Version.Digit.maxValue)
                of LESS | EQUAL => Scope (scopeFromVersion id)
                 | GREATER =>
                    Bindings (nodePushScope scopeFromVersion (Vector.sub (bindings, i)) id)
        in VectorExt.push (bindings, lastNode)
        end

    fun envPush env scopeFromVersion =
        let val res = ref NONE
        in env := bindingsPushScope (scopeFromVersion res) (!env) Version.empty
         ; valOf (!res)
        end

    fun pushOv env ov = envPush env (fn res => fn _ => ( res := SOME ()
                                                       ; Vector.fromList [Ov ov] ))

    fun pushUv env name =
        let fun scopeFromVersion res version = let val descr = {name, version, inScope = ref true}
                                                   val uv = ref (Root { descr, typ = ref NONE })
                                               in res := SOME uv
                                                ; Vector.fromList [Uv uv]
                                               end
        in envPush env scopeFromVersion
        end

    fun pushUvs env names =
        let fun uvFromVersion version name = let val descr = {name, version, inScope = ref true}
                                             in ref (Root {descr, typ = ref NONE})
                                             end
            fun scopeFromVersion res version =
                let val uvs = Vector.map (uvFromVersion version) names
                in res := SOME uvs
                 ; Vector.map Uv uvs
                end
        in envPush env scopeFromVersion
        end

    fun pushMarker env =
        let fun scopeFromVersion res version = ( res := SOME version
                                               ; Vector.fromList [] )
        in envPush env scopeFromVersion
        end

    fun pushScopedUv env name =
        let val marker = pushMarker env
            val uv = pushUv env name
        in (uv, marker)
        end

    fun insertUvBefore env succUv name =
        let val succVersion = #version (#descr (uvRoot succUv))
            val res = ref NONE
            fun scopeFromVersion version = let val descr = {name, version, inScope = ref true}
                                               val uv = ref (Root { descr, typ = ref NONE })
                                           in res := SOME uv
                                            ; Vector.fromList [Uv uv]
                                           end
            fun insert bindings digitIndex =
                let val isNotLastIndex = digitIndex < Version.length succVersion - 1
                    val version = if isNotLastIndex then succVersion else Version.pred succVersion
                    val digit = Version.Digit.toInt (Version.digit version digitIndex)
                    val node = Vector.sub (bindings, digit)
                    val bindings' = if isNotLastIndex
                                    then case node
                                         of Bindings bs => insert bs (digitIndex + 1)
                                          | Scope _ => raise Fail "unreachable"
                                    else nodePushScope scopeFromVersion node version
                in Vector.update (bindings, digit, Bindings bindings')
                end
        in env := insert (!env) 0
         ; valOf (!res)
        end

    fun dropDescr ({inScope, ...}: var_descr) = inScope := false

    val dropVar = fn Ov descr => dropDescr descr
                   | Uv uv => dropDescr (#descr (uvRoot uv))

    fun dropScope vars = Vector.app dropVar vars

    fun dropVars version node =
        let val rec dropAll = fn Bindings bs => Vector.app dropAll bs
                               | Scope s => dropScope s
            fun drop digitIndex =
                fn Bindings bs =>
                    let val digit = Version.Digit.toInt (Version.digit version digitIndex)
                        val pivot = Vector.sub (bs, digit)
                    in if digitIndex < Version.length version - 1
                       then drop (digitIndex + 1) pivot
                       else dropAll pivot
                     ; VectorSlice.app dropAll (VectorSlice.slice (bs, digit + 1, NONE))
                    end 
                 | Scope s => dropScope s
        in drop 0 (Bindings node)
        end

    fun truncate version node =
        let fun trunc digitIndex =
                fn Bindings bs =>
                    let val digit = Version.Digit.toInt (Version.digit version digitIndex)
                        val pivot = Vector.sub (bs, digit)
                        val isNotLastIndex = digitIndex < Version.length version - 1
                        val nKeep = if isNotLastIndex then digit + 1 else digit
                        val {update = update, done = done, ...} = MLton.Vector.create nKeep
                    in VectorSlice.appi (fn (i, v) =>
                                             case Int.compare (i, digit)
                                             of LESS => update (i, v)
                                              | EQUAL =>
                                                 update (i, Bindings (trunc (digitIndex + 1) pivot))
                                              | GREATER => raise Fail "unreachable")
                                        (VectorSlice.slice (bs, 0, SOME nKeep))
                     ; done ()
                    end
                 | Scope s => raise Fail "unreachable"
        in trunc 0 (Bindings node)
        end

    fun popVersion env version =
        ( dropVars version (!env)
        ; env := truncate version (!env) )

    fun popOv env (ov: ov) = popVersion env (#version ov)

    fun popUv env uv = popVersion env (#version (#descr (uvRoot uv)))

    val popMarker = popVersion

    fun ovInScope _ ({inScope, ...}: ov) = !inScope

    fun uvInScope _ uv = !(#inScope (#descr (uvRoot uv)))
end
