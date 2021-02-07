(* Predeclare types and signatures for typer internal modules so that they can be separated: *)

type span = Util.span
type 'a with_pos = 'a Ast.with_pos

type typ = Fc.Type.t

type 'a typing = {term : 'a; eff : typ}
type 'a kinding = {typ : 'a; kind : Fc.Type.kind}

module type KINDING = sig
    type env

    (*val kindof_F : span -> env -> Fc.Type.t -> Fc.Type.kind*)
    val kindof : env -> Ast.Type.t with_pos -> typ kinding
    val check : env -> Fc.Type.kind -> Ast.Type.t with_pos -> typ
    val check_nonquantifying : env -> Fc.Type.kind -> Ast.Type.t with_pos -> typ
    (*val eval : Util.span -> env -> typ -> (typ * typ Fc.Type.coercion option) option*)
    val eval : Util.span -> env -> typ -> typ
end

module type TYPING = sig
    type env

    val typeof : env -> Ast.Term.Expr.t with_pos -> Fc.Term.Expr.t typing
    val check : env -> typ -> Ast.Term.Expr.t with_pos -> Fc.Term.Expr.t typing
    (*val implement : env -> (Fc.Type.ov Vector.t * Fc.Type.t) -> Ast.Term.Expr.t with_pos
        -> Fc.Term.Expr.t typing
    val check_defs : env -> Ast.Term.Stmt.def Vector.t -> Fc.Term.Stmt.def Vector.t * env
    val check_stmt : env -> Ast.Term.Stmt.t -> Fc.Term.Stmt.t Vector.t typing * Fc.Type.t * env*)
    val check_interactive_stmts : env -> Ast.Term.Stmt.t Vector1.t -> Fc.Program.t typing * env
    (* HACK: (?): *)
    (*val elaborate_pat : env -> Ast.Term.Expr.pat with_pos ->
        Fc.Term.Expr.pat * (Fc.Type.ov Vector.t * Fc.Type.t) * Fc.Term.Expr.var Vector.t*)
end

module type MATCHING = sig
    type env

    val unify : span -> env -> typ -> typ -> unit
    val instance : span -> env -> typ -> typ -> unit
    (*val focalize : span -> env -> typ -> Fc.Type.template -> Coercer.t option * typ*)
    val solving_subtype : span -> env -> typ -> typ -> Coercer.t option
    val solving_unify : span -> env -> typ -> typ -> unit (*typ Fc.Type.coercion option*)
end

module type ENV = sig
    module T = Fc.Type

    type t

    val program : unit -> t
    val interactive : unit -> t
    val eval : unit -> t

    val find : t -> Util.span -> Name.t -> Fc.Term.Expr.var * bool
    val find_rhs : t -> Util.span -> Name.t -> Fc.Term.Expr.t typing
    val find_rhst : t -> Util.span -> Name.t -> Fc.Type.t kinding
    val implicits : t -> Fc.Term.Expr.var Streaming.Stream.t

    val t_scope : t -> T.scope

    val push_val : Util.plicity -> t -> Fc.Term.Expr.var -> t
    val push_level : t -> t * T.scope
    (*val push_rec : t
        -> ( Fc.Term.Expr.var Vector.t
           * ((*T.ov Vector.t * *) T.t) * Ast.Term.Expr.t with_pos ) CCVector.ro_vector
        -> t * Fc.Term.Expr.var list TxRef.t
    val push_row : t
        -> ( Fc.Term.Expr.var Vector.t
           * ((*T.ov Vector.t * *) T.t) * Ast.Type.t with_pos ) CCVector.ro_vector
        -> t * Fc.Term.Expr.var list TxRef.t
    val push_existential : t -> t * T.ov list TxRef.rref
    val push_skolems : t -> T.kind Vector.t -> t * T.ov Vector.t
    val push_axioms : t -> (Name.t * T.ov * uv) Vector.t -> t*)

    (*val generate : t -> T.binding -> T.binding * T.level*)

    (*val get_implementation : t -> T.ov -> (Name.t * T.ov * uv) option*)

(*
    val type_fns : t -> T.binding Vector.t

    val uv : t -> T.kind -> uv
    val sibling : t -> T.kind -> uv -> uv
    val get_uv : t -> uv -> Fc.Uv.v
    val set_uv : t -> span -> uv -> Fc.Uv.v -> unit

    val transaction : t -> (unit -> 'a) -> 'a
*)
(*
    val set_expr : t -> Fc.Term.Expr.t TxRef.rref -> Fc.Term.Expr.t -> unit
    val set_coercion : t -> typ T.coercion TxRef.rref -> typ T.coercion -> unit

    val document : t -> (Fc.Uv.subst -> 'a -> PPrint.document) -> 'a -> PPrint.document

    val expose : t -> T.t Vector.t -> T.t -> T.t
    val expose_template : t -> T.t Vector.t -> T.template -> T.template

    val close : t -> int Name.Map.t -> T.t -> T.t
    val close_template : t -> int Name.Map.t -> T.template -> T.template
    val close_coercion : t -> int Name.Map.t -> typ T.coercion -> typ T.coercion
*)
(*
    val reabstract : t -> T.t -> T.ov Vector.t * T.t
    val push_abs_skolems : t -> T.kind Vector1.t -> T.t -> t * T.ov Vector1.t * T.t
    val push_arrow_skolems : t -> T.kind Vector.t -> T.t -> T.t -> T.t
        -> t * T.ov Vector.t * T.t * T.t * T.t
    val push_impli_skolems : t -> T.kind Vector.t -> T.t -> T.t
        -> t * T.ov Vector.t * T.t * T.t
    val instantiate_abs : t -> T.kind Vector1.t -> T.t -> T.uv Vector1.t * T.t
    val instantiate_arrow : t -> T.kind Vector.t -> T.t -> T.t -> T.t
        -> T.uv Vector.t * T.t * T.t * T.t
    val instantiate_impli : t -> T.kind Vector.t -> T.t -> T.t
        -> T.uv Vector.t * T.t * T.t
    val instantiate_primop : t -> T.kind Vector.t -> T.t Vector.t -> T.t -> T.t
        -> T.uv Vector.t * T.t Vector.t * T.t * T.t
    val instantiate_branch : t -> T.kind Vector.t -> T.t Vector.t -> T.t -> T.t Vector.t
        -> T.uv Vector.t * T.t Vector.t * T.t * T.t Vector.t
*)

    val tv : t -> T.kind -> T.t

    val instantiate : t -> T.t -> T.t

    val reportError : t -> span -> TypeError.t -> unit
    val wrapErrorHandler : t -> ((span -> TypeError.t -> unit) -> (span -> TypeError.t -> unit)) -> t
end

module type EXPAND_PATS = sig
    type env

    type ctx = Inline | Shared of Fc.Term.Expr.var | Redirect of Fc.Term.Expr.var
    type final_naming = {tmp_var : Fc.Term.Expr.var; src_var : Fc.Term.Expr.var}
    type final_emitter = ctx -> final_naming Vector.t -> Fc.Term.Expr.t
    type clause' = {pat : Fc.Term.Expr.pat; emit : final_emitter}

    val expand_clauses : Util.span -> env -> Fc.Type.t -> Fc.Term.Expr.t -> clause' Vector.t
        -> Fc.Term.Expr.t
end

