************
Inlined Data
************

At least structs, variants and arrays can have non-word-sized fields. These can
be unboxed scalars or even other aggregates "inlined" as in C or Rust. This
simplifies complex FFI situations but also given better cache locality in
general. The cost of copying larger fields tends to be more than offset by the
locality benefits.

Any data type has three fundamental operations: allocation, storing into fields
and loading from them. (Compiler-generated) constructor functions store into
uninitialized fields and immutable fields are updated by copying the aggregate
and then storing, so more complex semantics consist of those three operations.

================
Loads and Stores
================

The offset and size can be looked up from the type info in the target header.
For stores the size could also be found in the field value header but the
offset has to be looked up from the target anyway.

==========
Allocation
==========

This is the tricky case. The aggregate value does not exist yet, so we can't
get the type descriptor from its header; on the contrary, we must create it and
store it into the header (or maybe we pass it into the allocation function and
the memory manager stores it for us, but that does not matter).

In the usual case where we initialize the allocation immediately we can compute
the type descriptor from the type descriptors of the field values. If the
aggregate is monomorphic the type descriptor can be computed statically (and
stored in the data segment of the final binary) or at least hoisted out of the
constructor function. If it is not monomorphic at least memoization could be
used.

However there is also the recursive case where a value is first allocated and
initialized later as it needs to be backpatched for recursion cycles. Here we
could just use the unoptimized version with a separate backpatching box (which
we always use in the MVP) if the type descriptor cannot be statically
determined.

==============
Mutable Fields
==============

Mutable fields of variant type are tricky because the variants often have
different sizes so we cannot just size the field for the initial value. Variants
of the same type should be forced to have the same size somehow (by preventing
them from being inlined?).

==============
Mutable Values
==============

Values with mutable fields cannot be inlined because they have to have a single
address for mutation to be shared between aliases simply.

======
Cycles
======

Recursive datatypes with no indirection would have infinite size. We need to
prevent that by forcing pointers at recursion points. For polymorphic data this
has to be done at runtime.

Polymorphic recursion? You can only have a finite number of instances at runtime
despite it?

Realistically cycles could only be constructed with mutable fields, which
prevent inlining anyway (e.g. general mutable graph nodes), or with variants
(e.g. singly-linked lists, binary trees etc.).

