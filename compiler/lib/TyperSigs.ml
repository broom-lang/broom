(* Predeclare types and signatures for typer internal modules so that they can be separated: *)

type span = Util.span
type 'a with_pos = 'a Ast.with_pos

type typ = Fc.Type.t

type 'a typing = {term : 'a; eff : typ}
type 'a kinding = {typ : 'a; kind : Fc.Type.kind}

(* Newtype to allow ignoring subtyping coercions without partial application warning: *)
(* TODO: triv_expr with_pos -> expr with_pos to avoid bugs that would delay side effects
         or that duplicate large/nontrivial terms: *)
type coercer = Cf of (Fc.Term.Expr.t -> Fc.Term.Expr.t) [@unboxed]

module type KINDING = sig
    type env

    val kindof_F : span -> env -> Fc.Type.t -> Fc.Type.kind
    val kindof : env -> Ast.Type.t with_pos -> typ kinding
    val check : env -> Fc.Type.kind -> Ast.Type.t with_pos -> typ
    val eval : env -> typ -> (typ * Fc.Type.coercion option) option
end

module type TYPING = sig
    type env

    val typeof : env -> Ast.Term.Expr.t with_pos -> Fc.Term.Expr.t typing
    val implement : env -> (Fc.Type.ov Vector.t * Fc.Type.t) -> Ast.Term.Expr.t with_pos
        -> Fc.Term.Expr.t typing
    val deftype : env -> Ast.Term.Stmt.def -> Fc.Term.Expr.def typing
    val check_stmt : env -> Ast.Term.Stmt.t -> Fc.Term.Stmt.t Vector.t typing * Fc.Type.t * env
    (* HACK: (?): *)
    val elaborate_pat : env -> Ast.Term.Expr.pat with_pos ->
        Fc.Term.Expr.pat * (Fc.Type.ov Vector.t * Fc.Type.t) * Fc.Term.Expr.var Vector.t
    val lookup : span -> env -> Name.t -> Fc.Term.Expr.var
end

module type MATCHING = sig
    type env

    val focalize : span -> env -> typ -> Fc.Type.template -> coercer * typ
    val solving_subtype : span -> env -> typ -> typ -> coercer
    val solving_unify : span -> env -> typ -> typ -> Fc.Type.coercion option
end

module type ENV = sig
    module T = Fc.Type

    type uv = Fc.Uv.t

    type t

    val interactive : unit -> t
    val eval : unit -> t

    val find : t -> Util.span -> Name.t -> Fc.Term.Expr.var
    val find_rhs : t -> Util.span -> Name.t -> Fc.Term.Expr.t typing
    val find_rhst : t -> Util.span -> Name.t -> Fc.Type.t kinding

    val push_val : t -> Fc.Term.Expr.var -> t
    val push_rec : t
        -> ( Fc.Term.Expr.var Vector.t
           * (T.ov Vector.t * T.t) * Ast.Term.Expr.t with_pos ) CCVector.ro_vector
        -> t * Fc.Term.Expr.var list TxRef.rref
    val push_row : t
        -> ( Fc.Term.Expr.var Vector.t
           * (T.ov Vector.t * T.t) * Ast.Type.t with_pos ) CCVector.ro_vector
        -> t * Fc.Term.Expr.var list TxRef.rref
    val push_existential : t -> t * T.ov list TxRef.rref
    val push_skolems : t -> T.kind Vector.t -> t * T.ov Vector.t
    val push_axioms : t -> (Name.t * T.ov * uv) Vector1.t -> t

    val generate : t -> T.binding -> T.binding * T.level

    val get_implementation : t -> T.ov -> (Name.t * T.ov * uv) option

    val uv : t -> T.kind -> Name.t -> uv
    val sibling : t -> T.kind -> uv -> uv
    val get_uv : t -> uv -> Fc.Uv.v
    val set_uv : t -> span -> uv -> Fc.Uv.v -> unit

    val set_expr : t -> Fc.Term.Expr.t TxRef.rref -> Fc.Term.Expr.t -> unit
    val set_coercion : t -> T.coercion TxRef.rref -> T.coercion -> unit

    val document : t -> (Fc.Uv.subst -> 'a -> PPrint.document) -> 'a -> PPrint.document

    val expose : t -> T.t Vector.t -> T.t -> T.t
    val expose_template : t -> T.t Vector.t -> T.template -> T.template

    val close : t -> int Name.Map.t -> T.t -> T.t
    val close_template : t -> int Name.Map.t -> T.template -> T.template

    val reabstract : t -> T.t -> T.ov Vector.t * T.t
    val push_abs_skolems : t -> T.kind Vector1.t -> T.t -> t * T.ov Vector1.t * T.t
    val push_arrow_skolems : t -> T.kind Vector.t -> (T.t, T.edomain) Ior.t -> T.t
        -> t * T.ov Vector.t * (T.t, T.edomain) Ior.t * T.t
    val instantiate_abs : t -> T.kind Vector1.t -> T.t -> T.uv Vector1.t * T.t
    val instantiate_arrow : t -> T.kind Vector.t -> (T.t, T.edomain) Ior.t
        -> T.t -> T.uv Vector.t * (T.t, T.edomain) Ior.t * T.t

    val reportError : t -> span -> TypeError.t -> unit
    val wrapErrorHandler : t -> ((span -> TypeError.t -> unit) -> (span -> TypeError.t -> unit)) -> t
end

