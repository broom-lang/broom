module Id = Id.Make ()

module Subst = struct
    type t = Obj.t Id.HashMap.t

    let current = ref Id.HashMap.empty
end

type 'a t = Id.t

let ref v =
    let id = Id.fresh () in
    Subst.current := Id.HashMap.add id (Obj.repr v) !Subst.current;
    Obj.magic id

let (!) (id : Id.t) = Obj.obj (Id.HashMap.get_exn (Obj.magic id) !Subst.current)

let (:=) (id : Id.t) v =
    Stdlib.(Subst.current := Id.HashMap.add (Obj.magic id) (Obj.repr v) !Subst.current)

