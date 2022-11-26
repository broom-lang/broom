open Fc
open Term
open Transactional.Ref

let rec eval_coercions co =
    let rec eval_coercion : Type.t Type.coercion -> Type.t Type.coercion = function
        | Patchable rco -> eval_coercion !rco
        | co -> co in

    Type.map_coercion_children eval_coercions (eval_coercion co)

let rec apply_expr_cos expr =
    let rec apply_co : Expr.t -> Expr.t = fun expr -> match expr.term with
        | Convert (rco, expr) ->
            let expr' = Coercer.apply !rco expr in
            if expr' == expr
            then expr'
            else apply_co expr'

        | Cast {castee; coercion} ->
            let coercion' = eval_coercions coercion in
            if coercion' == coercion
            then expr
            else Expr.at expr.pos expr.typ (Expr.cast castee coercion')

        | _ -> expr in

    Expr.map_children apply_expr_cos (apply_co expr)

let rec apply_pat_cos pat =
    let apply_co : Expr.pat -> Expr.pat = fun pat -> match pat.pterm with
        | View (f, arg) -> {pat with pterm = View (apply_expr_cos f, arg)}

        | PairP _ | ProxyP _
        | ConstP _
        | VarP _ | WildP _ -> Expr.map_pat_children apply_pat_cos pat in

    Expr.map_pat_children apply_pat_cos (apply_co pat)

let apply_def_cos (span, pat, expr) = (span, apply_pat_cos pat, apply_expr_cos expr)

let apply_coercions {Program.type_fns; defs; main} =
    { Program.type_fns
    ; defs = Vector.map apply_def_cos defs
    ; main = apply_expr_cos main }

