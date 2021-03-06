module Tx = Transactional
module Type = FcType.Type
type plicity = Util.plicity

module type EXPR = sig
    type def
    type stmt
    type coercer

    type var = {plicity : Util.plicity; name : Name.t; vtyp : Type.t}

    type t = {term : t'; typ : Type.t; pos : Util.span}

    and t' = private
        | Fn of {universals : Type.def Vector.t; param : var; body : t}
        | App of {callee : t; universals : Type.t Vector.t; arg : t}
        | PrimApp of {op : Primop.t; universals : Type.t Vector.t; args : t Vector.t}
        | PrimBranch of {op : Branchop.t; universals : Type.t Vector.t; args : t Vector.t
            ; clauses : prim_clause Vector.t}

        | Let of {defs : stmt Vector1.t; body : t}
        | Letrec of {defs : def Vector1.t; body : t}
        | LetType of {typedefs : Type.def Vector1.t; body : t}
        | Match of { matchee : t; clauses : clause Vector.t}

        | Axiom of { axioms : (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector1.t
            ; body : t }
        | Cast of {castee : t; coercion : Type.t Type.coercion}

        | Pack of {existentials : Type.t Vector1.t; impl : t}
        | Unpack of { existentials : Type.def Vector1.t; var : var; value : t; body : t }

        | Pair of {fst : t; snd : t}
        | Fst of t
        | Snd of t

        | Record of (Name.t * t) Vector.t
        | Where of {base : t; fields : (Name.t * t) Vector1.t}
        | With of {base : t; label : Name.t; field : t}
        | Select of {selectee : t; label : Name.t}

        | Proxy of Type.t
        | Const of Const.t

        | Use of var

        | Convert of coercer Tx.Ref.t * t

    and clause = {pat : pat; body : t}
    and prim_clause = {res : var option; prim_body : t}

    and pat = {pterm: pat'; ptyp : Type.t; ppos : Util.span}
    and pat' =
        | View of t * pat
        | PairP of {fst : pat; snd : pat}
        | ProxyP of Type.t
        | ConstP of Const.t
        | VarP of var
        | WildP of Name.t

    val var_to_doc : var -> PPrint.document
    val to_doc : t -> PPrint.document
    val pat_to_doc : pat -> PPrint.document

    val var : plicity -> Name.t -> Type.t -> var
    val fresh_var : plicity -> Type.t -> var

    val at : Util.span -> Type.t -> t' -> t
    val pat_at : Util.span -> Type.t -> pat' -> pat

    val fn : Type.def Vector.t -> var -> t -> t'
    val app : t -> Type.t Vector.t -> t -> t'
    val primapp : Primop.t -> Type.t Vector.t -> t Vector.t -> t'
    val primbranch : Branchop.t -> Type.t Vector.t -> t Vector.t -> prim_clause Vector.t -> t'
    val let' : stmt Vector.t -> t -> t'
    val letrec : def Vector.t -> t -> t'
    val axiom : (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector.t -> t -> t'
    val match' : t -> clause Vector.t -> t'
    val cast : t -> Type.t Type.coercion -> t'
    val pack : Type.t Vector.t -> t -> t'
    val unpack : Type.def Vector1.t -> var -> t -> t -> t'
    val pair : t -> t -> t'
    val fst : t -> t'
    val snd : t -> t'
    val record : (Name.t * t) Vector.t -> t'
    val where : t -> (Name.t * t) Vector.t -> t'
    val select : t -> Name.t -> t'
    val proxy : Type.t -> t'
    val const : Const.t -> t'
    val use : var -> t'
    val convert : coercer Tx.Ref.t -> t -> t'

    val map_children : (t -> t) -> t -> t
    val map_pat_children : (pat -> pat) -> pat -> pat

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
    val reify : Util.span -> Type.t -> t -> expr
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

