module Log = struct
    type t =
        { mutable nesting : int
        ; undos : (Obj.t ref * Obj.t) CCVector.vector }

    let log () = {nesting = 0; undos = CCVector.create ()}

    let record log ref v = CCVector.push log.undos (ref, v)

    let memento log = CCVector.length log.undos

    let abort =
        let rec loop undos memento i =
            if i >= memento
            then begin
                let (ref, v) = CCVector.get undos i in
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

type log = Log.t

type 'a std_ref = 'a ref
type 'a ref = 'a std_ref

let log = Log.log
let transaction = Log.transaction

let ref = ref
let get = (!)
let set : log -> 'a ref -> 'a -> unit = fun log ref v ->
    if log.nesting > 0
    then Log.record log (Obj.magic ref) (Obj.repr !ref);
    ref := v

