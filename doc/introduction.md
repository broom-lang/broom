# Introduction to Broom

**WIP warning: Things might not currently work as advertised here, or at all.**

## Definitions

Values can be named with `val`:

```
val answer: int = 42
```

You probably think of these as variables, but that is a questionable term since
name bindings are immutable and thus don't 'vary'.

## Blocks

`do` blocks provide statement sequencing. A statement is a definition or an
expression. The value of a `do` expression is the value of the last statement
if it is an expression and `{}` if it is a definition:

```
val n = 5
val m = do
    val squared = n * n
    ; squared + squared
end
```

The top level of programs is constrained to have no side effects (aside from
nontermination e.g. looping forever or crashing on an assertion). So expression
statements are useless there except at the end of blocks where their value is
used. However in other contexts expression statements can be useful for
performing side effects. Since the value of non-tail expression statements is
discarded it is constrained to be of type `{:}`, that is the information-free
`{}`. If you really want to discard a useful value of a side-effecting
expresssion, you can do so explicitly with `val _ = ...`.

Expression statements must be preceded by a semicolon to parse correctly.
Semicolons are also allowed before definitions and `end` so you can use your
preferred semicolon style:


```
# Pascal/Rust style:
val n = 5
val m = do
    val squared = n * n;
    squared + squared
end
```

```
# C style:
val n = 5
val m = do
    val squared = n * n;
    squared + squared;
end
```

The leading semicolon style looks odd at first but uses no redundant semicolons
and draws attention to expression statements that are often side-effecting and
thus error prone.

## Values

### Scalars

### Records

The empty or 'unit' record carries no information:

```
val empty: {:} = {}
```

The type of the empty record, `{:}` is syntactically distinct from the value.

Fields can be added to records with `with` syntax inside the record braces:

```
val point: {{:} with x : int, y : int} = {empty with x = 17, y = 23}
```

When extending the empty record (type), it can be elided so that

```
val point: {x : int, y : int} = {x = 17, y = 23}
```

is equivalent to the previous `point` definition.

`with` can only add fields, not replace existing ones. Override or 'functional
record update' is done with the syntactically similar `where`:

```
val point' = {point where x = 42}
```

(To be consistent with the type-level `where`, the new value must be a subtype
of the old one.)

Existing fields can be removed with `without`:

```
val point1D: {x : int} = {point without y}
```

(A combination of `with` and `without` can also be used to emulate `where` but
without the subtype check.)

Record fields can be read with the familiar dot notation:

```
val x: int = point'.x # = 42
```

### Variants

### Closed Algebraic Datatypes (Structs and Enums?)

## Functions

Like every functional (and nowadays even dysfunctional) language we have first
class functions:

```
val inc : int -> int = fn n -> n + 1 end
```

Functions support pattern matching:

```
val estimate : option int -> int = fn
    | Some n -> n
    | None -> 0
end
```

We also have definition sugar for the common case:

```
fun inc (n : int) = n + 1
```

### Parametrically Polymorphic ('Generic') Functions

First-class types and type paths can be used simply to provide parametrically
polymorphic (or 'generic') functions with universal-like types:

```
val identity : pi (a : type) -> a -> a =
    fn _ -> fn x -> x end end
val n = identity int 5
```

We do not have let-generalization so type parameters have to be explicitly
added to function definitions. However implicit parameters of type `type`
allow inferring type *arguments*:

```
val identity : pi (a : type) => a -> a =
    fn _ => fn x -> x end end
val n = identity 5
```

## Effects

Every expression has an effect row, which is only visible in function types.
Pure expressions have the empty effect row:

```
val inc : int -[]-> int = fn n -> n + 1 end
```

If that is the case the effect annotation can be elided:

```
val inc : int -> int = fn n -> n + 1 end
```

Side-effecting expressions have non-empty effect rows, e.g. `println`:

```
val println : string -[io : IO.t]-> {} =
    fn s -> print (s <> "\n")
```

Higher-order functions are often parametric in their effects:

```
val Array : ARRAY = module
    ...

    val map : pi a b (e : row) => (a -[e]-> b) -> t a -[e]-> t b
end
```

Obviously mapping a function over an array has no effects aside from those from
calling the callback function, which depend on the particular function.

## Modules

Modules are blocks that produce records of their bindings instead of the
value of the last expression:

```
val Point = module
    type t = {x : int, y : int}

    fun new x y = {x, y}
    val default = new 0 0
end

val origin : Point.t = Point.default
```

It would be possible to use a record-valued `do`-block instead but the `module`
syntax is more convenient and intentional when defining modules.

### Interfaces

Module interfaces are just the types of module values. We have `interface`
syntax to go with `module`:

```
type DEFAULT = interface
    type t

    val default : t
end
```

Interfaces are essential in providing encapsulation:

```
val DefaultPoint : DEFAULT = Point
```

Here upcasting the `Point` module to the `DEFAULT` interface hides both the
implementation of the `Point.t` type as a record and any associated operations
and values not found in the interface.

### Recursive Modules

Recursion across module boundaries is supported, even with sealing:

```
type FILE = interface
    type t
    val size : t -> int
end

val File : FILE = module
    extends @enum module
        type t
        val RegularFile : RegularFile.t -> t
        val Directory : Directory.t -> t
    end

    val size = fn
        | RegularFile f -> RegularFile.size f
        | Directory d -> Directory.size d
    end
end

val RegularFile : FILE = module
    type t = {name : string, size : int}

    fun size (f : t) = f.size
end

val Directory : FILE = module
    type t = {name : string, files : Array.t File.t}

    fun size ({_ with files}) =
        Array.foldl fn total f -> total + File.size f end
                    0 files
end
```

### Module Functions ('Functors')

Since we have first-class modules and functions, we also have module functions
(traditionally called 'functors' in ML modules). So we can define generic
abstractions in terms of modules, not just opaque types with no operations:

```
type ORD = interface
    type t

    val compare : t -> t -> order
end

type ORD_SET = interface
    type t
    type elem

    val empty : t
    val union : t -> t -> t
    
    ...
end

fun RedBlackSet (Elem : ORD) : ORD_SET where type elem = Elem.t = ...
```

Module functions behave 'applicatively' as in OCaml when their bodies are
free of side effects, so this works (unlike in Standard ML):

```
val IntSet = RedBlackSet(Int)
val IntSet' = RedBlackSet(Int)
val s = IntSet.union IntSet.empty IntSet'.empty
```

Impure module functions are 'generative' as in Standard ML, creating fresh
types on every call. The majority of module functions should be pure, even more
so than more usual functions.

## Implicits

Implicits can be used to make the type system fill in some values for you:

```
type ADD = interface
    type t

    val (+) : t -> t -> t
end

implicit val AddInt = Int

val (+) : pi Add : ADD => Add.t -> Add.t -> Add.t
    = fn Add => fn a -> fn b -> Add.+ a b

val n = 1 + 2 # Inferred to be `AddInt.+ 1 2`
```

Implicit functions can also be used to provide more complex inference:

```
implicit fun AddVec3D (?Elem : FIELD) = Vec3D(Elem)
val vec = Vec3D(Int).zero + Vec3D(Int).zero
# `val vec = AddVec3D(Int).+ (Vec3D(Int).zero) (Vec3D(Int).zero)`
```

Implicits are a general mechanism that can be used for other things as well but
usually we use it like this, to get more inference in generic code instead of
having to write somewhat tedious and verbose module code to perform various
dependency injections.

