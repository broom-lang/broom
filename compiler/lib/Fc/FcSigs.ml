module Tx = Transactional
module Type = FcType.Type

module type EXPR = sig
    type def
    type stmt
    type coercer

    and var = {name : Name.t; vtyp : Type.t}

    and t =
        { term : t'
        ; mutable parent : t option
        ; typ : Type.t
        ; pos : Util.span }

    and t' = private
        | Tuple of t array
        | Focus of {mutable focusee : t; index : int}

        | Fn of {universals : Type.def Vector.t; param : var; mutable body : t}
        | App of {mutable callee : t; universals : Type.t Vector.t; mutable arg : t}
        | PrimApp of {op : Primop.t; universals : Type.t Vector.t; mutable arg : t}
        | PrimBranch of {op : Branchop.t; universals : Type.t Vector.t; mutable arg : t
            ; clauses : prim_clause Vector.t}

        | Let of {defs : stmt Array1.t; mutable body : t}
        | Letrec of {defs : def Array1.t; mutable body : t}
        | LetType of {typedefs : Type.def Vector1.t; mutable body : t}
        | Match of {mutable matchee : t; clauses : clause Vector.t}

        | Axiom of { axioms : (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector1.t
            ; mutable body : t }
        | Cast of {mutable castee : t; coercion : Type.coercion}

        | Pack of {existentials : Type.t Vector1.t; mutable impl : t}
        | Unpack of { existentials : Type.def Vector1.t; var : var; mutable value : t
            ; mutable body : t }

        | Record of (Name.t * t) array
        | Where of {mutable base : t; fields : (Name.t * t) Array1.t}
        | With of {mutable base : t; label : Name.t; mutable field : t}
        | Select of {mutable selectee : t; label : Name.t}

        | Proxy of Type.t
        | Const of Const.t

        | Use of var

        | Convert of coercer option Tx.Ref.t * t

    and clause = {pat : pat; mutable body : t}
    and prim_clause = {res : var option; prim_body : t}

    and pat = {pterm: pat'; ptyp : Type.t; ppos : Util.span}
    and pat' =
        | TupleP of pat Vector.t
        | ProxyP of Type.t
        | ConstP of Const.t
        | VarP of var
        | WildP of Name.t

    val var_to_doc : var -> PPrint.document
    val to_doc : t -> PPrint.document
    val pat_to_doc : pat -> PPrint.document

    val var : Name.t -> Type.t -> var
    val fresh_var : Type.t -> var

    val at : Util.span -> Type.t -> t' -> t
    val pat_at : Util.span -> Type.t -> pat' -> pat

    val values : t Array.t -> t'
    val focus : t -> int -> t'
    val fn : Type.def Vector.t -> var -> t -> t'
    val app : t -> Type.t Vector.t -> t -> t'
    val primapp : Primop.t -> Type.t Vector.t -> t -> t'
    val primbranch : Branchop.t -> Type.t Vector.t -> t -> prim_clause Vector.t -> t'
    val let' : stmt Array.t -> t -> t'
    val letrec : def Array.t -> t -> t'
    val axiom : (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector.t -> t -> t'
    val match' : t -> clause Vector.t -> t'
    val cast : t -> Type.coercion -> t'
    val pack : Type.t Vector.t -> t -> t'
    val unpack : Type.def Vector1.t -> var -> t -> t -> t'
    val record : (Name.t * t) array -> t'
    val where : t -> (Name.t * t) array -> t'
    val select : t -> Name.t -> t'
    val proxy : Type.t -> t'
    val const : Const.t -> t'
    val use : var -> t'
    val convert : coercer option Tx.Ref.t -> t -> t'

    val map_children : (t -> t) -> t -> t

    module Var : Set.OrderedType with type t = var
    module VarSet : Set.S with type elt = var
end

module type COERCER = sig
    type expr

    type t

    val id : t
    val coercer : (expr -> expr) -> t
    val apply : t -> expr -> expr
    val apply_opt : t option -> expr -> expr
end

module type STMT = sig
    type expr
    type pat

    type def = Util.span * pat * expr

    type t
        = Def of def
        | Expr of expr

    val def_to_doc : def -> PPrint.document
    val to_doc : t -> PPrint.document

    val rhs : t -> expr
end

module type TERM = sig
    module rec Expr : (EXPR
        with type def = Stmt.def
        with type stmt = Stmt.t)

    and Stmt : (STMT
        with type expr = Expr.t
        with type pat = Expr.pat)
end

module type PROGRAM = sig
    module Term : TERM

    type t =
        { type_fns : Type.def Vector.t
        ; defs : Term.Stmt.def Vector.t
        ; main : Term.Expr.t }

    val to_doc : t -> PPrint.document
end

