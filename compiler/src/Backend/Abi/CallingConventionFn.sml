signature CALLING_CONVENTION = sig
    structure Location : LOCATION
    structure Register : REGISTER where type t = Location.Register.t

    type internal = Location.t vector

    type foreign =
        { args : Register.t vector
        , retVal : Register.t vector
        , callerSaves : Register.t vector
        , calleeSaves : Register.t vector }

    val isCallerSave : foreign -> Location.t -> bool
    val isCalleeSave : foreign -> Location.t -> bool
end

functor CallingConventionFn (Location : LOCATION) :> CALLING_CONVENTION
    where type Location.Register.t = Location.Register.t
    where type Location.t = Location.t
= struct
    structure Location = Location
    structure Register = Location.Register

    datatype loc = datatype Location.t

    type internal = Location.t vector

    type foreign =
        { args : Register.t vector
        , retVal : Register.t vector
        , callerSaves : Register.t vector
        , calleeSaves : Register.t vector }

    fun isCallerSave (cconv : foreign) =
        fn Register reg =>
            Vector.exists (fn reg' => Register.eq (reg', reg))
                          (#callerSaves cconv)
         | StackSlot _ => false

    fun isCalleeSave (cconv : foreign) =
        fn Register reg =>
            Vector.exists (fn reg' => Register.eq (reg', reg))
                          (#calleeSaves cconv)
         | StackSlot _ => true
end

