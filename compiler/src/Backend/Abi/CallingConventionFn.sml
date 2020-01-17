signature CALLING_CONVENTION = sig
    structure Register : REGISTER

    type internal = Register.t vector

    type foreign =
        { args : Register.t vector
        , retVal : Register.t vector
        , callerSaves : Register.t vector
        , calleeSaves : Register.t vector }

    val isCallerSave : foreign -> Register.t -> bool
    val isCalleeSave : foreign -> Register.t -> bool
end

functor CallingConventionFn (Register : REGISTER) :> CALLING_CONVENTION
    where type Register.t = Register.t
= struct
    structure Register = Register

    type internal = Register.t vector

    type foreign =
        { args : Register.t vector
        , retVal : Register.t vector
        , callerSaves : Register.t vector
        , calleeSaves : Register.t vector }

    fun isCallerSave (cconv : foreign) reg =
        Vector.exists (fn reg' => Register.eq (reg', reg))
                      (#callerSaves cconv)

    fun isCalleeSave (cconv : foreign) reg =
        Vector.exists (fn reg' => Register.eq (reg', reg))
                      (#calleeSaves cconv)
end

