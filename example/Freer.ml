signature FUNCTOR = sig
    type 'a t

    val map: ('a -> 'b) -> 'a t -> 'b t
end

signature MONAD = sig
    include FUNCTOR

    val pure: 'a -> 'a t
    val flatMap: ('a -> 'b t) -> 'a t -> 'b t
end

functor FreerMonad(Impl: FUNCTOR) :> MONAD = struct
    datatype 'a t = Fix of Impl.t ('a t)
                  | Pure of 'a
    
    val pure = Pure

    fun map f =
        fn Fix fv => Fix (Impl.map (map f) fv)
         | Pure v => Pure (f v)
    
    fun flatMap f =
        fn Fix fv => Fix (Impl.map (flatMap f) fv)
         | Pure v => f v
end

functor Reader(Env: sig type t end) = struct
    type 'a t = Get of Env.t -> 'a
    
    fun map f (Get k) = Get (f o k)
end

structure IntReader = Reader(struct type t = int end)

structure IntReaderMonad = FreerMonad(IntReader)

