open Asserts

module TS = TyperSigs
module AType = Ast.Type
module T = Fc.Type
module Env = TypeEnv
open Transactional.Ref

type 'a with_pos = 'a Util.with_pos

module Make (Typing : TS.TYPING) (Constraints : TS.CONSTRAINTS) = struct
    let elaborate _ (typ : AType.t with_pos) = todo (Some typ.pos)

    let check _ _ (typ : AType.t with_pos) = todo (Some typ.pos)

    let kindof_prim : Prim.t -> T.kind = function
        | Int | Bool | String -> T.aType
        | Array | Cell -> Pi {universals = Vector.empty; domain = T.aType; eff = EmptyRow
            ; codomain = T.aType}
        | SingleRep -> T.aType
        | Boxed -> Prim SingleRep
        | TypeIn -> Pi {universals = Vector.empty; domain = T.rep; eff = EmptyRow
            ; codomain = T.aType}
        | RowOf -> Pi {universals = Vector.empty; domain = T.aKind; eff = EmptyRow
            ; codomain = T.aKind}

    let rec kindof_F ctrs span env : T.t -> T.kind = function
        | Exists {existentials = _; body} -> kindof_F ctrs span env body
        | PromotedArray typs ->
            let el_kind = if Vector.length typs > 0
                then kindof_F ctrs span env (Vector.get typs 0)
                else Uv (Env.uv env false T.aKind) in
            App {callee = Prim Array; arg = el_kind}
        | PromotedTuple typs -> Tuple (Vector.map (kindof_F ctrs span env) typs)
        | Tuple typs ->
            let kinds = Vector.map (kindof_F ctrs span env) typs in
            App {callee = Prim TypeIn; arg = PromotedArray kinds}
        | Pi _ | Impli _ | Record _ | Proxy _ -> T.aType
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
            | ( Exists _ | PromotedArray _ | PromotedTuple _
              | Tuple _ | Pi _ | Impli _ | Record _ | With _ | EmptyRow | Proxy _ | Prim _ ) as typ ->
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
            | Exists _ | PromotedArray _ | PromotedTuple _
            | Tuple _ | Pi _ | Impli _ | Record _ | With _ | EmptyRow | Proxy _ ->
                unreachable (Some span) ~msg: "uncallable type in `eval.apply`"
            | Bv _ -> unreachable (Some span) ~msg: "`Bv` in `eval.apply`"
        in eval typ
end

