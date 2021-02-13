module type TYPE = FcTypeSigs.TYPE

module type EXPR = sig
    type typ
    type def
    type stmt

    and var = {name : Name.t; vtyp : typ}

    and typedef = Name.t * typ

    and t =
        { term : t'
        ; mutable parent : t option
        ; typ : typ
        ; pos : Util.span }

    and t' = private
        | Tuple of t array
        | Focus of {mutable focusee : t; index : int}

        | Fn of {t_scope : FcType.Uv.Scope.t; param : var; mutable body : t}
        | App of {mutable callee : t; universals : typ Vector.t; mutable arg : t}
        | PrimApp of {op : Primop.t; universals : typ Vector.t; mutable arg : t}
        | PrimBranch of {op : Branchop.t; universals : typ Vector.t; mutable arg : t
            ; clauses : prim_clause Vector.t}

        | Let of {defs : stmt Array1.t; mutable body : t}
        | Letrec of {defs : def Array1.t; mutable body : t}
        (*| LetType of {typedefs : typedef Vector1.t; mutable body : t}*)
        | Match of {mutable matchee : t; clauses : clause Vector.t}

        (*| Axiom of { axioms : (Name.t * Type.kind Vector.t * typ * typ) Vector1.t
            ; mutable body : t }*)
        | Cast of {mutable castee : t; coercion : FcType.Type.coercion}

        (*| Pack of {existentials : typ Vector1.t; mutable impl : t}
        | Unpack of { existentials : typedef Vector1.t; var : var; mutable value : t
            ; mutable body : t }*)

        | Record of (Name.t * t) array
        | Where of {mutable base : t; fields : (Name.t * t) Array1.t}
        | With of {mutable base : t; label : Name.t; mutable field : t}
        | Select of {mutable selectee : t; label : Name.t}

        | Proxy of typ
        | Const of Const.t

        | Use of var

        | Patchable of t TxRef.t

    and clause = {pat : pat; mutable body : t}
    and prim_clause = {res : var option; prim_body : t}

    and pat = {pterm: pat'; ptyp : typ; ppos : Util.span}
    and pat' =
        | TupleP of pat Vector.t
        | ProxyP of typ
        | ConstP of Const.t
        | VarP of var
        | WildP of Name.t

    val var_to_doc : var -> PPrint.document
    val to_doc : t -> PPrint.document
    val pat_to_doc : pat -> PPrint.document

    val var : Name.t -> typ -> var
    val fresh_var : typ -> var

    val at : Util.span -> typ -> t' -> t

    val tuple : t Array.t -> t'
    val focus : t -> int -> t'
    val fn : FcType.Uv.Scope.t -> var -> t -> t'
    val app : t -> typ Vector.t -> t -> t'
    val primapp : Primop.t -> typ Vector.t -> t -> t'
    val primbranch : Branchop.t -> typ Vector.t -> t -> prim_clause Vector.t -> t'
    val let' : stmt Array.t -> t -> t'
    val letrec : def Array.t -> t -> t'
    (*val axiom : (Name.t * Type.kind Vector.t * typ * typ) Vector.t -> t -> t'*)
    val match' : t -> clause Vector.t -> t'
    val cast : t -> FcType.Type.coercion -> t'
    (*val pack : typ Vector.t -> t -> t'
    val unpack : typedef Vector1.t -> var -> t -> t -> t'*)
    val record : (Name.t * t) array -> t'
    val where : t -> (Name.t * t) array -> t'
    val select : t -> Name.t -> t'
    val proxy : typ -> t'
    val const : Const.t -> t'
    val use : var -> t'
    val patchable : t TxRef.t -> t'

    val map_children : (t -> t) -> t -> t

    module Var : Set.OrderedType with type t = var
    module VarSet : Set.S with type elt = var
end

module type STMT = sig
    type expr
    type var

    type def = Util.span * var * expr

    type t
        = Def of def
        | Expr of expr

    val def_to_doc : def -> PPrint.document
    val to_doc : t -> PPrint.document

    val rhs : t -> expr
end

module type TERM = sig
    module rec Expr : (EXPR
        with type typ = FcType.Type.t
        with type def = Stmt.def
        with type stmt = Stmt.t)

    and Stmt : (STMT
        with type expr = Expr.t
        with type var = Expr.var)
end

module type PROGRAM = sig
    module Type : TYPE
    module Term : TERM

    type t =
        { type_fns : Term.Expr.typedef Vector.t
        ; defs : Term.Stmt.def Vector.t
        ; main : Term.Expr.t }

    val to_doc : t -> PPrint.document
end

