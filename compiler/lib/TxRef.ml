module type TRANSACTABLE = sig
    type log
    type contents
    type ref

    val ref : contents -> ref
    val get : ref -> contents
    val set : log -> ref -> contents -> unit
end

module type S = sig
    type log

    val log : unit -> log
    val transaction : log -> (unit -> 'a) -> 'a

    module Type : TRANSACTABLE
    module Expr : TRANSACTABLE
    module Uv : TRANSACTABLE
end

module type TRANSACTABLES = sig
    type typ
    type expr
    type uvv
end

module Make (Transactables : TRANSACTABLES) : S
    with type Type.contents = Transactables.typ
    with type Expr.contents = Transactables.expr
    with type Uv.contents = Transactables.uvv
= struct
    open Transactables

    module Log = struct
        type t =
            { mutable nesting : int
            ; type_sets : (typ ref * typ) CCVector.vector
            ; expr_sets : (expr ref * expr) CCVector.vector
            ; uv_sets : (uvv ref * uvv) CCVector.vector }

        let log () =
            { nesting = 0
            ; type_sets = CCVector.create ()
            ; expr_sets = CCVector.create ()
            ; uv_sets = CCVector.create () }

        let log_type_set log ref prev = CCVector.push log.type_sets (ref, prev)
        let log_expr_set log ref prev = CCVector.push log.expr_sets (ref, prev)
        let log_uv_set log ref prev = CCVector.push log.uv_sets (ref, prev)

        type memento =
            { type_length : int
            ; expr_length : int
            ; uv_length : int }

        let memento log =
            { type_length = CCVector.length log.type_sets
            ; expr_length = CCVector.length log.expr_sets
            ; uv_length = CCVector.length log.uv_sets }

        let abort_sublog sets length =
            let rec loop i =
                if i >= length
                then begin
                    let (ref, v) = CCVector.get sets i in
                    ref := v;
                    loop (i - 1)
                end in
            loop (CCVector.length sets - 1);
            CCVector.truncate sets length

        let abort log memento =
            abort_sublog log.type_sets memento.type_length;
            abort_sublog log.expr_sets memento.expr_length;
            abort_sublog log.uv_sets memento.uv_length;
            log.nesting <- log.nesting - 1

        let commit log memento =
            CCVector.truncate log.type_sets memento.type_length;
            CCVector.truncate log.expr_sets memento.expr_length;
            CCVector.truncate log.uv_sets memento.uv_length;
            log.nesting <- log.nesting - 1

        let transaction log body =
            let mem = memento log in
            try
                log.nesting <- log.nesting + 1;
                let res = body () in
                commit log mem;
                res
            with
            | exn ->
                abort log mem;
                raise exn
    end

    module type TRANSACTABLE_KERNEL = sig
        type t

        val log_set : Log.t -> t ref -> t -> unit
    end

    module Transactable (Contents : TRANSACTABLE_KERNEL) : TRANSACTABLE
        with type contents = Contents.t
    = struct
        type log = Log.t
        type contents = Contents.t

        type 'a std_ref = 'a ref
        type ref = contents std_ref

        let ref = ref
        let get = (!)
        let set (log : log) ref v =
            if log.nesting > 0
            then Contents.log_set log ref !ref;
            ref := v
    end

    type log = Log.t

    let log = Log.log
    let transaction = Log.transaction

    module Type = Transactable(struct
        type t = typ
        let log_set = Log.log_type_set
    end)

    module Expr = Transactable(struct
        type t = expr
        let log_set = Log.log_expr_set
    end)

    module Uv = Transactable(struct
        type t = uvv
        let log_set = Log.log_uv_set
    end)
end

