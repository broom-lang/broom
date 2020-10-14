open Cps
module Builder = Program.Builder
module FExpr = Fc.Term.Expr

module Env : sig
    type t

    val empty : t
end = struct
    module Map = CCHashTrie.Make (struct
        type t = int
        let equal = (=)
        let hash = Hashtbl.hash
    end)

    type t = Expr.Id.t Map.t

    let empty = Map.empty
end

type meta_cont =
    | FnK of (stid: Expr.Id.t -> vid: Expr.Id.t -> Transfer.t)

let convert_typ : Fc.Type.t -> Type.t = function
    | Prim p -> Prim p
    | _ -> failwith "TODO: convert_typ"

let convert state_typ ({type_fns; defs; main = main_body} : Fc.Program.t) =
    let builder = Builder.create type_fns in
    let state_typ = convert_typ state_typ in
    let (main_span, main_body) =
        let pos =
            ( (if Vector.length defs > 0
              then (let (pos, _, _) = Vector.get defs 0 in fst pos)
              else fst main_body.pos)
            , snd main_body.pos ) in
        let codomain = main_body.typ in
        (pos, FExpr.at pos codomain (FExpr.letrec (Vector.to_array defs) main_body)) in

    let rec convert parent state k (_ : Env.t) (expr : FExpr.t) = match expr.term with
        | Const c ->
            let typ = convert_typ expr.typ in
            Builder.express builder {pos = expr.pos; cont = parent; typ; term = Const c}
            |> continue k state

        | _ -> failwith "TODO: CpsConvert.convert.convert"

    and continue k stid vid = match k with
        | FnK k -> k ~stid ~vid in

    let convert_export pos name params (body : FExpr.t) =
        let id = Cont.Id.fresh () in
        let parent = Some id in
        let codomain = convert_typ body.typ in
        let state =
            Builder.express builder {pos; cont = parent; typ = state_typ
                ; term = Const (Int 0)} in (* FIXME *)
        let k = FnK (fun ~stid: _ ~vid ->
            {pos; term = Return (Vector.singleton codomain, Vector.singleton vid)}) in
        let env = Env.empty in
        let cont : Cont.t =
            { pos; name; universals = Vector.empty; params
            ; body = convert parent state k env body } in
        Builder.add_cont builder id cont;
        id in

    let main_id = convert_export main_span None Vector.empty main_body in
    Builder.build builder main_id

