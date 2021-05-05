open Asserts

module TS = TyperSigs
module AType = Ast.Type
module T = Fc.Type
module Env = TypeEnv
open Transactional.Ref

type 'a with_pos = 'a Util.with_pos
type 'a kinding = 'a TS.kinding

module Make (Typing : TS.TYPING) (Constraints : TS.CONSTRAINTS) = struct
    let elaborate ctrs env (typ : AType.t with_pos) =
        let rec elab env (typ : AType.t with_pos) : T.t kinding =
            match typ.v with
            | Tuple typs ->
                (match Vector.length typs with
                | 0 -> {typ = Prim Unit; kind = App {callee = Prim TypeIn; arg = Prim UnitRep}}

                | 2 ->
                    let fst_rep = T.Uv (Env.uv env false (Prim Rep)) in
                    let fst = check env (T.App {callee = Prim TypeIn; arg = fst_rep}) (Vector.get typs 0) in
                    let snd_rep = T.Uv (Env.uv env false (Prim Rep)) in
                    let snd = check env (App {callee = Prim TypeIn; arg = snd_rep}) (Vector.get typs 1) in
                    let rep = T.App {callee = App {callee = Prim PairRep; arg = fst_rep}; arg = snd_rep} in
                    {TS.typ = Pair {fst; snd}; kind = App {callee = Prim TypeIn; arg = rep}}

                | _ -> unreachable (Some typ.pos))

            | _ -> todo (Some typ.pos)

        and check env kind ({Util.pos = span; _} as typ) =
            let {TS.typ; kind = kind'} = elab env typ in
            ignore (Constraints.unify ctrs span env kind' kind);
            typ in

        let (env, existentials) = Env.push_existential env in
        let {TS.typ; kind} = elab env typ in
        let typ : T.t = match Vector1.of_list !existentials with
            | Some existentials ->
                let (_, substitution) = Vector1.fold (fun (i, substitution) {T.name; _} ->
                    (i + 1, Name.Map.add name i substitution)
                ) (0, Name.Map.empty) existentials in
                Exists {existentials = existentials |> Vector1.map (fun {T.kind; _} -> kind)
                    ; body = T.close substitution typ}
            | None -> typ in
        {TS.typ; kind}

    let check ctrs env kind (({pos = span; _} as typ) : AType.t with_pos) =
        let {TS.typ; kind = kind'} = elaborate ctrs env typ in
        ignore (Constraints.unify ctrs span env kind' kind);
        typ

    let kindof_prim : Prim.t -> T.kind = function
        | Unit -> (* TypeIn UnitRep *)
            App {callee = Prim TypeIn; arg = Prim UnitRep}

        | Int | Bool | String -> T.aType
        | Array | Cell -> Pi {universals = Vector.empty; domain = T.aType; eff = EmptyRow
            ; codomain = T.aType}
        | Rep -> T.aType
        | Boxed -> Prim Rep

        | UnitRep -> Prim Rep
        | PairRep -> (* Rep -> Rep -> Rep *)
            Pi {universals = Vector.empty; domain = Prim Rep; eff = EmptyRow
                ; codomain = Pi {universals = Vector.empty; domain = Prim Rep; eff = EmptyRow
                    ; codomain = Prim Rep}}

        | TypeIn -> (* Rep -> Type *)
            Pi {universals = Vector.empty; domain = Prim Rep; eff = EmptyRow
                ; codomain = T.aType}

        | RowOf -> Pi {universals = Vector.empty; domain = T.aKind; eff = EmptyRow
            ; codomain = T.aKind}

    let rec kindof_F ctrs span env : T.t -> T.kind = function
        | Exists {existentials = _; body} -> kindof_F ctrs span env body
        | Pi _ | Impli _ | Record _ | Proxy _ -> T.aType

        | Pair {fst; snd} -> (* TypeIn (PairRep fst_rep snd_rep) *)
            let fst_rep = T.Uv (Env.uv env false (Prim Rep)) in
            check_F ctrs span env (T.App {callee = Prim TypeIn; arg = fst_rep}) fst;
            let snd_rep = T.Uv (Env.uv env false (Prim Rep)) in
            check_F ctrs span env (T.App {callee = Prim TypeIn; arg = snd_rep}) snd;
            let rep = T.App {callee = App {callee = Prim PairRep; arg = fst_rep}; arg = snd_rep} in
            App {callee = Prim TypeIn; arg = rep}

        | With _ | EmptyRow -> T.aRow
        | Fn {param = domain; body} -> Pi { universals = Vector.empty; domain; eff = EmptyRow
            ; codomain = kindof_F ctrs span env body }
        | App {callee; arg} ->
            (match kindof_F ctrs span env callee with
            | Pi {universals; domain; eff = _; codomain} ->
                if Vector.length universals = 0 then begin
                    check_F ctrs span env domain arg;
                    codomain
                end else todo (Some span) ~msg: "universals in type application"
            | _ -> unreachable (Some span) ~msg: "invalid type application in `kindof_F`.")
        | Ov _ -> todo (Some span) (*((_, kind), _) -> kind*)
        | Bv _ -> todo (Some span) (*{kind; _} -> kind*)
        | Uv uv -> (match !uv with
            | Unassigned (_, _, kind, _) -> kind
            | Assigned typ -> kindof_F ctrs span env typ)
        | Prim pt -> kindof_prim pt

    and check_F ctrs span env kind typ =
        let kind' = kindof_F ctrs span env typ in
        ignore (Constraints.unify ctrs span env kind' kind)

    let eval span _ typ =
        let (let*) = Option.bind in
        let (let+) = Fun.flip Option.map in

        let rec eval = function
            | T.App {callee; arg} ->
                let* (callee, callee_co) = eval callee in
                let+ (typ, co) = apply callee arg in
                ( typ
                , match (callee_co, co) with
                  | (Some callee_co, Some co) ->
                      Some (T.Trans (Inst (callee_co, Vector1.singleton arg), co))
                  | (Some callee_co, None) -> Some (Inst (callee_co, Vector1.singleton arg))
                  | (None, Some co) -> Some co
                  | (None, None) -> None )
            | Fn _ as typ -> Some (typ, None)
            | Ov _ (*ov as typ*) -> todo (Some span)
                (*(match Env.get_implementation env ov with
                | Some (axname, _, uv) ->
                    let typ = T.Uv uv in
                    let+ (typ, co) = eval typ in
                    ( typ
                    , match co with
                      | Some co -> Some (T.Trans (AUse axname, co))
                      | None -> Some (AUse axname) )
                | None -> Some (typ, None))*)
            | Uv uv as typ ->
                (match !uv with
                | Assigned typ -> eval typ (* OPTIMIZE: path compression *)
                | Unassigned (false, _, _, _) -> Some (typ, None)
                | Unassigned (true, _, _, _) -> None)
            | ( Exists _ | Pi _ | Impli _ | Pair _ | Record _ | With _ | EmptyRow | Proxy _ | Prim _ ) as typ ->
                Some (typ, None)
            | Bv _ -> unreachable (Some span) ~msg: "`Bv` in `eval`"

        and apply callee arg = match callee with
            (* NOTE: Arg kinds do not need to be checked here because all `App`s originate from functors: *)
            | T.Fn _ -> todo (Some span) (*{param = _; body} -> eval (Env.expose env (Vector.singleton arg) body)*)
            | Ov _ | App _ | Prim _ -> Some (T.App {callee; arg}, None)
            | Uv uv ->
                (match !uv with
                | Unassigned _ -> None
                | Assigned _ -> unreachable (Some span) ~msg: "Assigned in `apply`.")
            | Exists _ | Pi _ | Impli _ | Pair _ | Record _ | With _ | EmptyRow | Proxy _ ->
                unreachable (Some span) ~msg: "uncallable type in `eval.apply`"
            | Bv _ -> unreachable (Some span) ~msg: "`Bv` in `eval.apply`"
        in eval typ
end

