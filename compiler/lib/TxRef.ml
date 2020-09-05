module Log = struct
    type t =
        { mutable nesting : int
        ; refs : Obj.t ref CCVector.vector
        ; vals : Obj.t CCVector.vector }

    let log () =
        { nesting = 0
        ; refs = CCVector.create ()
        ; vals = CCVector.create () }

    let record : t -> 'a ref -> unit = fun log ref ->
        let ref = Obj.magic ref in
        CCVector.push log.refs ref;
        CCVector.push log.vals !ref

    let memento log = CCVector.length log.refs

    let abort =
        let rec loop refs vals memento i =
            if i >= memento
            then begin
                let ref = CCVector.get refs i in
                let v = CCVector.get vals i in
                ref := v;
                loop refs vals memento (i - 1)
            end in
        fun ({nesting = _; refs; vals} as log) memento ->
            loop refs vals memento (CCVector.length refs - 1);
            CCVector.truncate refs memento;
            CCVector.truncate vals memento;
            log.nesting <- log.nesting - 1

    let commit log memento =
        CCVector.truncate log.refs memento;
        CCVector.truncate log.vals memento;
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
    then Log.record log ref;
    ref := v;
    log

let eq : 'a store -> 'a rref -> 'a rref -> 'a store * bool
= fun log ref ref' -> (log, ref == ref')

