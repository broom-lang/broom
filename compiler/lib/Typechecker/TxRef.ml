module Log = struct
    type t =
        { mutable nesting : int
        ; refs : Obj.t ref CCVector.vector
        ; vals : Obj.t CCVector.vector
        ; mutable id_counter : int }

    let log () =
        { nesting = 0
        ; refs = CCVector.create ()
        ; vals = CCVector.create () 
        ; id_counter = 0 }

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
        fun ({nesting = _; refs; vals; id_counter = _} as log) memento ->
            loop refs vals memento (CCVector.length refs - 1);
            CCVector.truncate refs memento;
            CCVector.truncate vals memento;
            log.nesting <- log.nesting - 1

    let commit log memento =
        let nesting' = log.nesting - 1 in
        log.nesting <- nesting';
        if nesting' = 0 then begin
            CCVector.truncate log.refs memento;
            CCVector.truncate log.vals memento;
        end

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

type log = Log.t

type 'a rref = 'a ref

let log = Log.log
let transaction = Log.transaction

let fresh_id (log : log) =
    let id = log.id_counter in
    log.id_counter <- id + 1;
    id

let ref = ref

let (!) = (!)

let set (log : Log.t) ref v =
    if log.nesting > 0
    then Log.record log ref;
    ref := v

let eq : 'a rref -> 'a rref -> bool = (==)

(* OPTIMIZE: Allocating tuples just to satisfy UnionFind.STORE: *)
module Store = struct
    type 'a store = log

    type 'a rrref = 'a rref
    type 'a rref = 'a rrref

    let new_store = log

    let make log v = (log, ref v)
    let get log ref = (log, !ref)
    let set log ref v = set log ref v; log
    let eq log ref ref' = (log, eq ref ref')
end

