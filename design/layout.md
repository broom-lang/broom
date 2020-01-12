# Memory Layouts

Most of this is implementation-dependent and can also be affected by
compiler optimizations.

Assuming 64-bit throughout.

## Heap Object Slot Types

One of

* Ptr at offset, size 8 bytes, raw pointer
* Poly at offset, size 8 bytes, tagged value
* Scalar at offset, of size

## Heap Objects

* Structs
* Variants
* Arrays
* Closures are just structs starting with 8 byte scalar for code address
* Records are just arrays of Poly slots, slot per field
* Polymorphic variants are two words; one Ptr for tag symbol and one Poly for
  value

## Heap Object Headers

## Scalars in Registers

Scalar values in registers are in native unboxed format if their type is
statically monomorphic. Scalar values need to be (un)boxed when passed to/from
polymorphic locations (e.g. through polymorphic functions or heap slots).

## Boxing Scheme

Tagged pointers, 3-bit tags on 64-bit and 2-bit tags on 32-bit.

* 64-bit integers need to be heap-allocated and then tagged as pointers. The
  heap layout is that of a struct with one 64-bit scalar field.

## Finding pointers

### Roots

* A (failed) safepoint
    1. saves all definitely non-pointer (i.e. monomorphic scalar) registers on
       the stack (or in callee-save registers).
    2. saves all potentially pointer (i.e. the remaining) registers on the stack
       and passes the pointer and length of that array to the runtime system.
    3. the runtime system scans that array just like heap object slots,
       potentially overwriting elements with their new addresses.
    4. garbage collection proceeds
    5. safepoint restores registers and restarts the allocation

### Scanning

* If the slot is definitely a pointer, check that it is non-null
  (i.e. initialized by the mutator), mark ref (and overwrite slot if moving GC).
* If the slot is not necessarily a pointer, check that the MSB is 1, convert
  into a canonical pointer, mark ref, re-tag (and overwrite slot if moving GC).

## Allocation

* Freshly allocated memory is zeroed.
* Allocator stores layout header and returns pointer to start of actual object.

