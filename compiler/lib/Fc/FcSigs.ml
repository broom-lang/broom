module type TYPE = FcTypeSigs.TYPE

module type EXPR = sig
    module Type : TYPE

    type def

    and var =
        { name : Name.t; vtyp : Type.t; mutable value : t option
        ; uses : use CCVector.vector }

    and use = {mutable expr : t option; mutable var : var}

    and t =
        { term : t'
        ; mutable parent : t option
        ; typ : Type.t
        ; pos : Util.span }

    and t' =
        | Values of t array
        | Focus of {mutable focusee : t; index : int}

        | Fn of {universals : Type.binding Vector.t; param : var; mutable body : t}
        | App of {mutable callee : t; universals : Type.t Vector.t; mutable arg : t}
        | PrimApp of {op : Primop.t; universals : Type.t Vector.t; mutable arg : t}

        | Let of {def : def; mutable body : t}
        | Letrec of {defs : def Array1.t; mutable body : t}
        | LetType of {typedefs : Type.binding Vector1.t; mutable body : t}
        | Match of {mutable matchee : t; clauses : clause Vector.t}

        | Axiom of { axioms : (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector1.t
            ; mutable body : t }
        | Cast of {mutable castee : t; coercion : Type.coercion}

        | Pack of {existentials : Type.t Vector1.t; mutable impl : t}
        | Unpack of { existentials : Type.binding Vector1.t; var : var; mutable value : t
            ; mutable body : t }

        | Record of (Name.t * t) array
        | Where of {mutable base : t; fields : (Name.t * t) Array1.t}
        | With of {mutable base : t; label : Name.t; mutable field : t}
        | Select of {mutable selectee : t; label : Name.t}

        | Proxy of Type.t
        | Const of Const.t

        | Use of use

        | Patchable of t TxRef.rref

    and clause = {pat : pat; mutable body : t}

    and pat = {pterm: pat'; ptyp : Type.t; ppos : Util.span}
    and pat' =
        | ValuesP of pat Vector.t
        | ProxyP of Type.t
        | ConstP of Const.t
        | VarP of var
        | WildP

    val var_to_doc : var -> PPrint.document
    val to_doc : Type.subst -> t -> PPrint.document
    val pat_to_doc : Type.subst -> pat -> PPrint.document

    val var : Name.t -> Type.t -> t option -> var
    val fresh_var : Type.t -> t option -> var

    val at : Util.span -> Type.t -> t' -> t

    (* TODO: Add more of these: *)
    val letrec : def Array.t -> t -> t'
    val use : var -> t'

    val map_children : (t -> t) -> t -> t
end

module type STMT = sig
    module Type : TYPE

    type expr
    type var

    type def = Util.span * var * expr

    type t
        = Def of def
        | Expr of expr

    val def_to_doc : Type.subst -> def -> PPrint.document
    val to_doc : Type.subst -> t -> PPrint.document

    val rhs : t -> expr
end

module type TERM = sig
    module Type : TYPE

    module rec Expr : (EXPR
        with module Type = Type
        with type def = Stmt.def)

    and Stmt : (STMT
        with module Type = Type
        with type expr = Expr.t
        with type var = Expr.var)
end

