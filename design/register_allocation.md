# Register Allocation

* Register allocation works on Extended Basic Blocks. An EBB is a tree of
  continuations where only the root is exported, escapes into a closure or is
  called more than once.
* The EBB is traversed in post order which is reverse to the order of
  execution. The continuation contents are also traversed backwards, first the
  final control transfer and then the other instructions from last to first.
  This avoids the need for a separate liveness analysis prepass and also makes
  "online" register targeting possible without prepasses or lookaheads. This
  whole backwards trick is inspired by LuaJIT and Mono as well as the Larceny
  Scheme compiler Twobit.
* So we always start at a transfer. Furthermore the transfer must be a direct
  or indirect unconditional branch because
    1. Critical edges are not allowed so conditional branches can never be EBB
       leaves.
    2. FFI calls cannot have TCO since that would elide our one and only native
       stack frame. So they are never at tail position.
* The leaf transfer will have a number of arguments and possibly use a register
  as an indirect call target as well.
    - For a direct call, get the target parameter registers and assign them to
      the arguments. If the target did not have parameter registers assigned,
      assign them first in some conventional way somewhat like closures or the
      foreign ABI. Note that this may assign multiple registers to a def
      since the same argument can be passed for multiple parameters.
    - For an indirect call, assign the argument registers according to the
      fixed user function / continuation calling convention. Allocate some
      other register for the indirection, there should be some available at
      this point.
    - Then just emit the unconditional branch without any arguments (and with
      the allocated indirection register).
* Regular instructions
* CISC complications
    - Fixed registers (e.g. mul on accumulator register)
    - Two-operand code
* Multiple results (e.g. from mul, div)
* Foreign calls
* Foreign callbacks
    - Callee-save registers
* Conditional branches and merging register environments there
* Stack spills not due to foreign calls
* Parameter spills (i.e. known function has too many parameters to fit in
  registers)
* Safepoints

