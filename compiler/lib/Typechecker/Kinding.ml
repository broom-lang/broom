open Asserts

module AType = Ast.Type
module T = Fc.Type
module Env = TypeEnv
open Transactional.Ref

type 'a with_pos = 'a Util.with_pos

module Make (Typing : TyperSigs.TYPING) = struct
    let elaborate _ (typ : AType.t with_pos) = todo (Some typ.pos)

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
                | Unassigned _ -> Some (typ, None))
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

