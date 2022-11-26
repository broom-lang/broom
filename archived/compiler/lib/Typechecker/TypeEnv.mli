module T = Fc.Type
module FExpr = Fc.Term.Expr
type var = FExpr.var
module Tx = Transactional
type span = Util.span

type val_binding =
    | White of {span : span; pat : Ast.Expr.t; expr : Ast.Expr.t}
    | Grey of {span : span; pat : Ast.Expr.t; expr : Ast.Expr.t}
    | Black of {span : span; pat : FExpr.pat; expr : FExpr.t option}

type row_binding =
    | WhiteT of {span : span; pat : Ast.Expr.t; typ : Ast.Expr.t}
    | GreyT of span
    | BlackT of {span : span; typ : T.t}

type nonrec_scope = var Name.HashMap.t * val_binding Tx.Ref.t

type rec_scope = (var * val_binding Tx.Ref.t) Name.HashMap.t

type row_scope = (var * row_binding Tx.Ref.t) Name.HashMap.t

type scope =
    | Hoisting of T.ov list Tx.Ref.t * T.level
    | Rigid of T.ov Vector.t
    | NonRec of nonrec_scope
    | Rec of rec_scope
    | Row of row_scope

type env

module NonRecScope : sig
    type t = nonrec_scope

    module Builder : sig
        type scope = t
        type t

        val create : unit -> t
        val var : env -> t -> Util.plicity -> Name.t -> var
        val build : t -> span -> FExpr.pat -> FExpr.t option -> scope
    end
end

module RecScope : sig
    type t = rec_scope

    module Builder : sig
        type scope = t
        type t

        val create : unit -> t
        val binding : t -> span -> Ast.Expr.t -> Ast.Expr.t -> val_binding Tx.Ref.t
        val var : env -> t -> val_binding Tx.Ref.t -> Util.plicity -> Name.t -> var
        val build : t -> scope
    end
end

module RowScope : sig
    type t = row_scope

    module Builder : sig
        type scope = t
        type t

        val create : unit -> t
        val binding : t -> span -> Ast.Expr.t -> Ast.Expr.t -> row_binding Tx.Ref.t
        val var : env -> t -> row_binding Tx.Ref.t -> Util.plicity -> Name.t -> var
        val build : t -> scope
    end
end

type t = env

val empty : t
val toplevel : Namespace.t -> t

val namespace : t -> Namespace.t option
val type_fns : t -> T.def Vector.t

type error_handler = TypeError.t -> unit

val report_error : t -> error_handler
val with_error_handler : t -> error_handler -> t

val scopes : t -> scope list

val push_param : t -> var -> FExpr.pat -> t
val push_nonrec : t -> NonRecScope.t -> t
val push_rec : t -> RecScope.t -> t
val push_row : t -> RowScope.t -> t

val find_val : t -> Name.t -> (var * val_binding Tx.Ref.t * t) option

val implicits : t -> FExpr.var Streaming.Stream.t

val push_existential : t -> t * T.ov list Transactional.Ref.t
val generate : t -> T.def -> T.ov
val reabstract : t -> T.t -> T.ov Vector.t * T.t

val push_abs_skolems : t -> T.kind Vector1.t -> T.t -> t * T.ov Vector1.t * T.t
val instantiate_abs : t -> T.kind Vector1.t -> T.t -> T.uv Vector1.t * T.t

val push_arrow_skolems : t -> T.kind Vector.t -> T.t -> T.t -> T.t
    -> t * T.ov Vector.t * T.t * T.t * T.t
val instantiate_arrow : t -> T.kind Vector.t -> T.t -> T.t -> T.t
    -> T.uv Vector.t * T.t * T.t * T.t

val push_impli_skolems : t -> T.kind Vector.t -> T.t -> T.t
    -> t * T.ov Vector.t * T.t * T.t
val instantiate_impli : t -> T.kind Vector.t -> T.t -> T.t
    -> T.uv Vector.t * T.t * T.t

val instantiate_primop : t -> T.kind Vector.t -> T.t Vector.t -> T.t -> T.t
    -> T.uv Vector.t * T.t Vector.t * T.t * T.t
val instantiate_branch : t -> T.kind Vector.t -> T.t Vector.t -> T.t -> T.t Vector.t
    -> T.uv Vector.t * T.t Vector.t * T.t * T.t Vector.t

val uv : t -> bool -> T.kind -> T.uv
val some_type_kind : t -> bool -> T.t

