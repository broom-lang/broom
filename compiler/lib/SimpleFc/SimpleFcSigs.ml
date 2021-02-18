module type EXPR = sig
    module Type = SyntacticType

    type typ = Type.t
    type kind = Type.kind
    type decl
    type stmt

    type def = Name.t * typ

    type t =
        { term : t'
        ; mutable parent : t option
        ; typ : typ
        ; pos : Util.span }

    and t' = private
        | Use of Name.t

        | Fn of {universals : (Name.t * kind) Vector.t; param : def; mutable body : t}
        | App of {mutable callee : t; universals : typ Vector.t
            ; mutable arg : t}
        | PrimApp of {op : Primop.t; universals : typ Vector.t
            ; mutable arg : t}
        | PrimBranch of {op : Branchop.t; universals : typ Vector.t
            ; mutable arg : t; clauses : prim_clause Vector.t}

        | Let of {decls : stmt Array1.t; mutable body : t}
        | Letrec of {decls : decl Array1.t; mutable body : t}
        | Match of {mutable matchee : t; clauses : clause Vector.t}

        (*| Axiom of { axioms : (Name.t * Type.kind Vector.t * typ * typ) Vector1.t
            ; mutable body : t }*)
        | Cast of {mutable castee : t; coercion : Type.coercion}

        | Record of (Name.t * t) array
        | Where of {mutable base : t; fields : (Name.t * t) Array1.t}
        | With of {mutable base : t; label : Name.t; mutable field : t}
        | Select of {mutable selectee : t; label : Name.t}
        | Tuple of t array
        | Focus of {mutable focusee : t; index : int}

        | Proxy of typ
        | Const of Const.t

    and clause = {pat : pat; mutable body : t}
    and prim_clause = {res : Name.t option; prim_body : t}

    and pat = {pterm: pat'; ptyp : typ; ppos : Util.span}
    and pat' =
        | ProxyP of typ
        | ConstP of Const.t
        | VarP of Name.t
        | WildP of Name.t

    val def_to_doc : def -> PPrint.document
    val to_doc : t -> PPrint.document
    val pat_to_doc : pat -> PPrint.document

    val at : Util.span -> typ -> t' -> t

    val fn : Type.def Vector.t -> Name.t * typ -> t -> t'
    val app : t -> typ Vector.t -> t -> t'
    val primapp : Primop.t -> typ Vector.t -> t -> t'
    val primbranch : Branchop.t -> typ Vector.t -> t -> prim_clause Vector.t -> t'
    val let' : stmt Array.t -> t -> t'
    val letrec : decl Array.t -> t -> t'
    (*val axiom : (Name.t * Type.kind Vector.t * typ * typ) Vector.t -> t -> t'*)
    val match' : t -> clause Vector.t -> t'
    val cast : t -> Type.coercion -> t'
    val record : (Name.t * t) array -> t'
    val where : t -> (Name.t * t) array -> t'
    val with' : t -> Name.t -> t -> t'
    val select : t -> Name.t -> t'
    val tuple : t Array.t -> t'
    val focus : t -> int -> t'
    val proxy : typ -> t'
    val const : Const.t -> t'
    val use : Name.t -> t'
end

module type STMT = sig
    module Type = SyntacticType

    type expr

    type decl = Util.span * Name.t * Type.t * expr

    type t
        = Decl of decl
        | Expr of expr

    val decl_to_doc : decl -> PPrint.document
    val to_doc : t -> PPrint.document
end

