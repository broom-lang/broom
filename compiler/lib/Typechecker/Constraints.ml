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

    let solve_subtype_whnf _ _ _ _ _ = Asserts.todo None

    let solve_subtype ctrs span env sub super _ =
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

    let solve_unify_whnf _ _ _ _ _ = Asserts.todo None

    let solve_unify ctrs span env ltyp rtyp _ =
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

    let solve ctrs =
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
    let unify ctrs span env ltyp rtyp =
        let coercion = Tx.Ref.ref (T.Refl rtyp) in
        Tx.Queue.push ctrs (Unify {span; env; ltyp; rtyp; coercion});
        Some (T.Patchable coercion)

    (* OPTIMIZE: First try to subtype on the fly: *)
    let subtype ctrs span env sub super =
        let coerce = Tx.Ref.ref Coercer.id in
        Tx.Queue.push ctrs (Subtype {span; env; sub; super; coerce});
        Some (Coercer.coercer (fun expr -> E.at span super (E.convert coerce expr)))
end

