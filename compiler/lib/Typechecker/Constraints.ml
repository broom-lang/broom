open Asserts

module TS = TyperSigs
module T = FcType.Type
module E = Fc.Term.Expr
module Coercer = Fc.Term.Coercer
module Tx = Transactional
open Constraint
open Tx.Ref

module Make (K : TS.KINDING) = struct
    type queue = Constraint.queue

(* # Solvers *)
 
    let occurs_check span env uv typ =
        let rec check : T.t -> unit = function
            | Exists {existentials = _; body} -> check body
            | PromotedArray typs -> Vector.iter check typs
            | PromotedTuple typs -> Vector.iter check typs
            | Tuple typs -> Vector.iter check typs
            | Pi {universals = _; domain; eff; codomain} -> check domain; check eff; check codomain
            | Impli {universals = _; domain; codomain} -> check domain; check codomain
            | Record row -> check row
            | With {base; label = _; field} -> check base; check field
            | EmptyRow -> ()
            | Proxy carrie -> check carrie
            | Fn {param = _; body} -> check body
            | App {callee; arg} -> check callee; check arg
            | Ov _ (*ov*) -> todo (Some span)
                (*(match Env.get_implementation env ov with
                | Some (_, _, uv') -> check (Uv uv')
                | None -> ())*)
            | Uv uv' ->
                (match !uv' with
                | Unassigned _ ->
                    if uv = uv'
                    then Env.report_error env {v = Occurs (uv, typ); pos = span}
                    else ()
                | Assigned typ -> check typ)
            | Bv _ | Prim _ -> () in
        check typ

    (* Occurs check, ov escape check, HKT capturability check and uv level updates.
       Complected for speed. *)
    let check_uv_assignee span env uv level max_uv_level typ =
        let rec check : T.t -> unit = function
            | Exists {existentials = _; body} -> check body
            | PromotedArray typs -> Vector.iter check typs
            | PromotedTuple typs -> Vector.iter check typs
            | Tuple typs -> Vector.iter check typs
            | Pi {universals = _; domain; eff; codomain} -> check domain; check eff; check codomain
            | Impli {universals = _; domain; codomain} -> check domain; check codomain
            | Record row -> check row
            | With {base; label = _; field} -> check base; check field
            | EmptyRow -> ()
            | Proxy carrie -> check carrie
            | Fn {param = _; body} -> check body
            | App {callee; arg} -> check callee; check arg
            | Ov _ -> todo (Some span) (*((_, level') as ov) ->
                (match Env.get_implementation env ov with
                | Some (_, _, uv') -> check (Uv uv')
                | None ->
                    if level' <= level
                    then ()
                    else Env.reportError env pos (Escape ov))*)
            | Uv uv' ->
                (match !uv' with
                | Unassigned (name, kind, level') ->
                    if uv = uv'
                    then Env.report_error env {v = Occurs (uv, typ); pos = span}
                    else if level' <= level
                    then ()
                    else if level' <= max_uv_level
                    then uv' := (Unassigned (name, kind, level)) (* hoist *)
                    else Env.report_error env {v = IncompleteImpl (uv, uv'); pos = span}
                | Assigned typ -> check typ)
            | Bv _ | Prim _ -> () in
        check typ

    let rec solve_subtype_whnf ctrs span env sub super = match (sub, super) with
        (* TODO: uv impredicativity clashes *)
        (* FIXME: prevent nontermination from impredicative instantiation: *)
        | (T.Uv uv, T.Uv uv') when Tx.Ref.eq uv uv' -> None
        | (Uv _, Uv _) -> todo (Some span)
        | (Uv uv, _) ->
            (match !uv with
            | Unassigned (_, kind, _) ->
                occurs_check span env uv super;
                ignore (unify ctrs span env kind (K.kindof_F ctrs span env super));
                uv := Assigned super;
                None
            | Assigned _ -> unreachable (Some span) ~msg: "Assigned `typ` in `subtype_whnf`")
        | (_, Uv uv) ->
            (match !uv with
            | Unassigned (_, kind, _) ->
                occurs_check span env uv sub;
                ignore (unify ctrs span env (K.kindof_F ctrs span env sub) kind);
                uv := Assigned sub;
                None
            | Assigned _ -> unreachable (Some span) ~msg: "Assigned `super` in `subtype_whnf`")

        | (Prim sub_p, super) -> (match super with
            | Prim super_p when Prim.eq sub_p super_p -> None
            | _ ->
                Env.report_error env {v = Subtype (sub, super); pos = span};
                None)

        | _ -> todo (Some span) ~msg: (Util.doc_to_string (T.to_doc sub) ^ " <: "
            ^ Util.doc_to_string (T.to_doc super))

    and solve_subtype ctrs span env sub super _ =
        let (let*) = Option.bind in
        let (let+) = Fun.flip Option.map in

        let* (sub', co) = K.eval span env sub in
        let+ (super', co') = K.eval span env super in
        let coerce = solve_subtype_whnf ctrs span env sub' super' in
        (match (co, coerce, co') with
        | (Some co, Some coerce, Some co') -> Some (Coercer.coercer (fun v ->
            let castee = Coercer.apply coerce (E.at span sub' (E.cast v co)) in
            E.at span super (E.cast castee (Symm co'))))
        | (Some co, Some coerce, None) -> Some (Coercer.coercer (fun v ->
            Coercer.apply coerce (E.at span sub' (E.cast v co))))
        | (Some co, None, Some co') -> Some (Coercer.coercer (fun v ->
            E.at span super (E.cast v (Trans (co, Symm co')))))
        | (Some co, None, None) -> Some (Coercer.coercer (fun v ->
            E.at span super (E.cast v co)))
        | (None, Some coerce, Some co') -> Some (Coercer.coercer (fun v ->
            E.at span super (E.cast (Coercer.apply coerce v) (Symm co'))))
        | (None, Some coerce, None) -> Some coerce
        | (None, None, Some co') -> Some (Coercer.coercer (fun v ->
            E.at span super (E.cast v co')))
        | (None, None, None) -> None)

    and solve_unify_whnf ctrs span env ltyp rtyp = match (ltyp, rtyp) with
        (* TODO: uv impredicativity clashes: *)
        | (T.Uv uv, T.Uv uv') when Tx.Ref.eq uv uv' -> None
        | (Uv _, Uv _) -> todo (Some span)
        | (Uv uv, typ') | (typ', Uv uv) ->
            (match !uv with
            | Unassigned (_, kind, level) ->
                check_uv_assignee span env uv level Int.max_int typ';
                ignore (unify ctrs span env (K.kindof_F ctrs span env typ') kind);
                uv := Assigned typ';
                None
            | Assigned _ -> unreachable (Some span) ~msg: "Assigned `typ` in `unify_whnf`")

        | (EmptyRow, rtyp) -> (match rtyp with
            | EmptyRow -> None
            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | _ -> todo (Some span) ~msg: (Util.doc_to_string (T.to_doc ltyp) ^ " ~ "
            ^ Util.doc_to_string (T.to_doc rtyp))

    and solve_unify ctrs span env ltyp rtyp _ =
        let (let*) = Option.bind in
        let (let+) = Fun.flip Option.map in

        let* (ltyp, co) = K.eval span env ltyp in
        let+ (rtyp, co'') = K.eval span env rtyp in
        let co' = solve_unify_whnf ctrs span env ltyp rtyp in
        (match (co, co', co'') with
        | (Some co, Some co', Some co'') -> Some (T.Trans (Trans (co, co'), Symm co''))
        | (Some co, Some co', None) -> Some (Trans (co, co'))
        | (Some co, None, Some co'') -> Some (Trans (co, Symm co''))
        | (Some co, None, None) -> Some co
        | (None, Some co', Some co'') -> Some (Trans (co', Symm co''))
        | (None, Some co', None) -> Some co'
        | (None, None, Some co'') -> Some (Symm co'')
        | (None, None, None) -> None)

    and solve ctrs =
        let solve1 = function
            | Subtype {span; env; sub; super; coerce} as ctr ->
                (match solve_subtype ctrs span env sub super coerce with
                | Some co -> coerce := (match co with
                    | Some co -> co
                    | None -> Coercer.id)
                | None -> Tx.Queue.push ctrs ctr)

            | Unify {span; env; ltyp; rtyp; coercion} as ctr ->
                (match solve_unify ctrs span env ltyp rtyp coercion with
                | Some co -> coercion := (match co with
                    | Some co -> co
                    | None -> Refl rtyp)
                | None -> Tx.Queue.push ctrs ctr) in

        (* FIXME: Ensure termination: *)
        let rec loop () =
            match Tx.Queue.pop ctrs with
            | Some ctr ->
                solve1 ctr;
                loop ()
            | None -> () in
        loop ()

(* # Generators *)

    (* OPTIMIZE: First try to unify on the fly: *)
    and unify ctrs span env ltyp rtyp =
        let coercion = Tx.Ref.ref (T.Refl rtyp) in
        Tx.Queue.push ctrs (Unify {span; env; ltyp; rtyp; coercion});
        Some (T.Patchable coercion)

    (* OPTIMIZE: First try to subtype on the fly: *)
    and subtype ctrs span env sub super =
        let coerce = Tx.Ref.ref Coercer.id in
        Tx.Queue.push ctrs (Subtype {span; env; sub; super; coerce});
        Some (Coercer.coercer (fun expr -> E.at span super (E.convert coerce expr)))
end

