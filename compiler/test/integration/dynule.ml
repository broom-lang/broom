type DEFAULT = interface
    type t
    val default: t
end

val Dyfault: DEFAULT =
    if True
    then module
             type t = Int
             val default = 0
         end
    else module
             type t = {:}
             val default = {}
         end

