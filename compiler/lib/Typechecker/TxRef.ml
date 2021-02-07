module Id = Id.Make ()

module Subst = struct
    type t = Obj.t Id.HashMap.t

    let current = ref Id.HashMap.empty
end

type 'a t = Id.t

let equal r r' = Id.equal (Obj.magic r) (Obj.magic r')

let hash r = Id.hash (Obj.magic r)

let ref v =
    let id = Id.fresh () in
    Subst.current := Id.HashMap.add id (Obj.repr v) !Subst.current;
    Obj.magic id

let (!) (id : Id.t) = Obj.obj (Id.HashMap.get_exn (Obj.magic id) !Subst.current)

let (:=) (id : Id.t) v =
    Subst.current := Id.HashMap.add (Obj.magic id) (Obj.repr v) Stdlib.(!Subst.current)

type 'a txref = 'a t

module Hashtbl = struct
    module Make (T : sig type t end) = CCHashtbl.Make (struct
        type t = T.t txref

        let equal = equal
        let hash = hash
    end)
end

