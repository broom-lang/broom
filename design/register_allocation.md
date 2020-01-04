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
* Regular 'statement' instructions
    1. If a target def has no register, allocate a register for it, moving
       and loading other defs if necessary
    2. If a target def has a stack slot, emit a store to it
    2. Free the registers of target defs
    3. Look up / allocate registers for source operands, moving and loading
       other defs if necessary
    4. Emit the instruction itself
* CISC complications
    - Fixed registers (e.g. mul on accumulator register)
    - Two-operand code
    - Taking advantage of memory operands
* Multiple results (e.g. from mul, div)
* Foreign calls
    - non-reentrant
        1. Emit restoration code for defs in caller-save registers. Start with
           moves from free callee-save registers. If that is not enough, use
           loads from the stack.
        2. Free the registers of the target defs (return values)
        3. For an indirect call, allocate a register for the indirection,
           emitting a load if something else needs to be spilled
        4. Popping stack arguments
        4. Emit the call instruction
        5. Argument shuffling and stack-pushing
    - reentrant
* Foreign callbacks
    - Callee-save registers
    - Returns
* Conditional branches and merging register environments there
* Continuation parameters
    - If the continuation has no register assignment for the parameters, set
      its parameter assignment to the current one. If there are unused
      parameters (not found in register environment) leave those unassigned,
      to be filled in later at calls (at this point all known continuations
      will have at least one call).
* Stack spills not due to foreign calls
* Parameter spills (i.e. known function has too many parameters to fit in
  registers)
* Safepoints

## Allocating a Register

This is the case where any (general-purpose) register will do. This happens
when a def is encountered for the first time in the backward traversal, as an
instruction operand including indirect call destinations (call arguments are
always subject to either constraints or some convention) or as an unused target
def. Any moves and loads mentioned here are emitted before (executed after) the
instruction itself.

1. Use a free register, preferring callee-save ones
2. Otherwise see if some defs have copies in multiple registers. Choose one of
   the registers so occupied with some heuristic and evict it by emitting a
   move to it from some other (heuristic) register of that def.
3. Otherwise choose another def by some heuristic and spill it by emitting a
   load to it from a free stack slot.

