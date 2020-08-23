module Make (C : TyperSigs.TYPING) (M : TyperSigs.MATCHING) : TyperSigs.ELABORATION = struct

module AType = Ast.Type
module T = Fc.Type

type 'a with_pos = 'a Util.with_pos

let elaborate : Env.t -> AType.t with_pos -> T.abs
= fun env typ -> match typ.v with
    | Record decls ->
        if Vector.length decls = 0
        then Fc.Type.to_abs (Record (Vector.empty ()))
        else failwith "TODO: nonempty signature"

and eval env typ =
    let (>>=) = Option.bind in

    let rec eval = function
        | T.App (callee, args) ->
            eval callee >>= fun (callee, callee_co) ->
            apply callee args |> Option.map (fun (typ, co) ->
            ( typ
            , match (callee_co, co) with
              | (Some callee_co, Some co) -> Some (T.Trans (Inst (callee_co, args), co))
              | (Some callee_co, None) -> Some (Inst (callee_co, args))
              | (None, Some co) -> Some co
              | (None, None) -> None ))
        | Fn _ as typ -> Some (typ, None)
        (*| Ov ov as typ ->
            (match Env.get_implementation env ov with
            | Some (axname, _, uv) ->
                let typ = Uv uv in
                eval typ |> Option.map (fun (typ, co) ->
                ( typ
                , match co with
                  | Some co -> Some (Trans (AUse axname, co))
                  | None -> Some (AUse axname) ))
            | None -> Some (typ, None))*)
        | Uv uv as typ ->
            (match Env.get_uv env uv with
            | Assigned typ -> eval typ
            | Unassigned _ -> Some (typ, None))
        | (Pi _ | Record _ | Type _ | Prim _) as typ -> Some (typ, None)
        | Bv _ -> failwith "unreachable: `Bv` in `whnf`"
        | Use _ -> failwith "unreachable: `Use` in `whnf`"

    and apply callee args = match callee with
        | T.Fn body -> eval (T.expose (Env.uv_substr env) (Vector1.to_vector args) body)
        | Ov _ | App _ -> Some (T.App (callee, args), None)
        | Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned _ -> None
            | Assigned _ -> failwith "unreachable: Assigned in `apply`.")
        | Pi _ | Record _ | Type _ | Prim _ -> failwith "unreachable: uncallable type in `whnf`"
        | Bv _ -> failwith "unreachable: `Bv` in `whnf/apply`"
        | Use _ -> failwith "unreachable: `Use` in `whnf/apply`"
    in eval typ
end

