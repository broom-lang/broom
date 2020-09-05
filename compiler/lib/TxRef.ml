module Log = struct
    type undo = Undo : 'a ref * 'a -> undo

    (* OPTIMIZE: Struct of Arrays?: *)
    type t =
        { mutable nesting : int
        ; undos : undo CCVector.vector }

    let log () = {nesting = 0; undos = CCVector.create ()}

    let record log ref v = CCVector.push log.undos (Undo (ref, v))

    let memento log = CCVector.length log.undos

    let abort =
        let rec loop undos memento i =
            if i >= memento
            then begin
                let Undo (ref, v) = CCVector.get undos i in
                ref := v;
                loop undos memento (i - 1)
            end in
        fun ({nesting = _; undos} as log) memento ->
            loop undos memento (CCVector.length undos - 1);
            CCVector.truncate undos memento;
            log.nesting <- log.nesting - 1

    let commit log memento =
        CCVector.truncate log.undos memento;
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

type 'a store = Log.t

type 'a rref = 'a ref

let new_store = Log.log
let transaction = Log.transaction

(* OPTIMIZE: Allocating tuples just to satisfy UnionFind.STORE: *)

let make log v = (log, ref v)

let get log ref = (log, !ref)

let set (log : Log.t) ref v =
    if log.nesting > 0
    then Log.record log ref !ref;
    ref := v;
    log

let eq : 'a store -> 'a rref -> 'a rref -> 'a store * bool
= fun log ref ref' -> (log, ref == ref')

