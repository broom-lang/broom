type span = Util.span

module type TYPE = CpsSigs.TYPE

module type EXPR = sig
    type t = Cps.Expr.t'

    val to_doc : t -> PPrint.document
    val is_pure : t -> bool

    module Id = Cps.Expr.Id
end

module type STMT = sig
    module Type : TYPE
    module Expr : EXPR
    type var = Expr.Id.t

    type t' = var Vector.t * Expr.t
    type t = {pos : span; typ : Type.t; term : t'}

    val to_doc : t -> PPrint.document
    val iter_labels : (Cps.Cont.Id.t -> unit) -> t -> unit
    val iter_uses : (Expr.Id.t -> unit) -> t -> unit
end

module type TRANSFER = sig
    module Type : TYPE
    module Pattern = Cps.Pattern
    type expr_id
    type cont_id

    type clause = Cps.Transfer.clause

    type t' =
        | Goto of {callee : cont_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Jump of {callee : expr_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Match of {matchee : expr_id; clauses : clause Vector.t}
        | PrimApp of {op : Branchop.t; universals : Type.t Vector.t
            ; args : expr_id Vector.t; clauses : clause Vector.t}
        | Return of Type.t Option.t * expr_id Option.t

    type t = {pos : span; term : t'}

    val to_doc : t -> PPrint.document
    val iter_labels : (cont_id -> unit) -> t -> unit
    val iter_uses : (expr_id -> unit) -> t -> unit
end

module type CONT = sig
    module Type : TYPE
    module Expr : EXPR
    module Stmt : STMT
    module Transfer : TRANSFER

    module Id : Id.S

    type param = Expr.Id.t * Type.t

    type t =
        { pos : span
        ; name : Name.t option
        ; universals : Type.param Vector.t
        ; params : param Vector.t
        ; stmts : Stmt.t Vector.t
        ; transfer : Transfer.t }

    val def_to_doc : Id.t -> t -> PPrint.document
end

module type PROGRAM = sig
    module Type : TYPE
    module Expr : EXPR
    module Stmt : STMT
    module Transfer : TRANSFER
    module Cont : CONT

    type t
    type builder

    val to_doc : t -> PPrint.document

    val cont : t -> Cont.Id.t -> Cont.t
    val exports : t -> Cont.Id.t Streaming.Source.t
    val main : t -> Cont.Id.t

    module Builder : sig
        val create : Fc.Type.def Vector.t -> Cont.Id.t -> builder
        val add_cont : builder -> Cps.Cont.Id.t -> Cps.Cont.t -> unit
        val cont_mem : builder -> Cps.Cont.Id.t -> bool
        val define : builder -> Cont.Id.t -> Stmt.t -> unit
        val add_param : builder -> Cont.Id.t -> int -> Expr.Id.t -> unit
        val set_transfer : builder -> Cps.Cont.Id.t -> Transfer.t -> unit
        val build : builder -> t
        
        type t = builder
    end
end

