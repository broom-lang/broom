type span = Util.span

module type TYPE = CpsSigs.TYPE

module type EXPR = sig
    type t = Cps.Expr.t'

    val to_doc : t -> PPrint.document

    module Id = Cps.Expr.Id
end

module type STMT = sig
    module Type : TYPE
    module Expr : EXPR
    type var = Expr.Id.t

    type t' =
        | Def of var * Expr.t
        | Expr of Expr.t

    type t = {pos : span; typ : Type.t; term : t'}

    val to_doc : t -> PPrint.document
end

module type TRANSFER = sig
    module Type : TYPE
    type expr_id
    type cont_id

    type clause = Cps.Transfer.clause

    type t' =
        | Goto of {callee : cont_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Jump of {callee : expr_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Match of {matchee : expr_id; clauses : clause Vector.t}
        | Return of Type.t Vector.t * expr_id Vector.t

    type t = {pos : span; term : t'}

    val to_doc : t -> PPrint.document
end

module type CONT = sig
    module Type : TYPE
    module Stmt : STMT
    module Transfer : TRANSFER

    type t =
        { pos : span
        ; name : Name.t option
        ; universals : Type.param Vector.t
        ; params : Type.t Vector.t
        ; stmts : Stmt.t Vector.t
        ; transfer : Transfer.t }

    val to_doc : t -> PPrint.document

    module Id : Id.S
end

module type PROGRAM = sig
    module Stmt : STMT
    module Transfer : TRANSFER
    module Cont : CONT

    type t
    type builder

    val to_doc : t -> PPrint.document

    module Builder : sig
        val create : Fc.Type.binding Vector.t -> Cont.Id.t -> builder
        val add_cont : builder -> Cps.Cont.Id.t -> Cps.Cont.t -> unit
        val cont_mem : builder -> Cps.Cont.Id.t -> bool
        val define : builder -> Cont.Id.t -> Stmt.t -> unit
        val set_transfer : builder -> Cps.Cont.Id.t -> Transfer.t -> unit
        val build : builder -> t
        
        type t = builder
    end
end

