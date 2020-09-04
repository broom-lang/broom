*********************
Introduction to Broom
*********************

*WIP warning: Things might not currently work as advertised here, or at all.*

Definitions
===========

Values can be named::

    val answer: int = 42;

You probably think of these as variables, but that is a questionable term since
name bindings are immutable and thus don't 'vary'.

Blocks
======

``do`` blocks provide statement sequencing. A statement is a definition or an
expression. The value of a ``do`` expression is the value of the last statement
if it is an expression and ``{}`` if it is a definition::

    n = 5;
    m = do {
        squared = n * n;
        squared + squared -- trailing semicolon is optional
    }

The top level of programs is constrained to have no side effects (aside from
nontermination e.g. looping forever or crashing on an assertion). So expression
statements are useless there except at the end of blocks where their value is
used. However in other contexts expression statements can be useful for
performing side effects. Since the value of non-tail expression statements is
discarded it is constrained to be of type ``{|}``, that is the information-free
``{}``. If you really want to discard a useful value of a side-effecting
expresssion, you can do so explicitly with ``_ = ...``.

Values
======

Scalars
-------

Records
-------

The empty or 'unit' record carries no information::

    empty : {|} = {}

The type of the empty record, ``{|}`` is syntactically distinct from the value.

Fields can be added to records with the infix operator ``with``::

    point : {|} with {|x : int; y : int|} = empty with {x = 17; y = 23}

When extending the empty record (type), it can be elided so that::

    point : {|x : int; y : int|} = {x = 17; y = 23}

is equivalent to the previous ``point`` definition.

``with`` can only add fields, not replace existing ones. Override or
'functional record update' is done with another infix operator ``where``::

    point' = point where {x = 42}

(To be consistent with the type-level ``where``, the new value must be a
subtype of the old one.)

Existing fields can be removed with ``without``::

    point1D : {|x : int|} = point without {y}

(A combination of ``with`` and ``without`` can also be used to emulate
``where`` but without the subtype check.)

Record fields can be read with the familiar dot notation::

    x : int = point'.x -- = 42

Variants
--------

Closed Algebraic Datatypes (Structs and Enums?)
-----------------------------------------------

Functions
=========

Like every functional (and nowadays even dysfunctional) language we have first
class functions::

    inc : int -> int = [| n -> n + 1]

Functions support pattern matching::

    estimate : Option.t int -> int = [
        | Some n -> n
        | None -> 0
    ]

We also have definition sugar for the common case::

    fun inc (n : int) = n + 1

Parametrically Polymorphic ('Generic') Functions
------------------------------------------------

First-class types and type paths can be used simply to provide parametrically
polymorphic (or 'generic') functions with universal-like types::

    identity : pi (a : type, _ : a) -> a = [| _ x -> x];
    n = identity int 5;

We do not have let-generalization so type parameters have to be explicitly
added to function definitions. However implicit parameters of type ``type``
allow inferring type **arguments**::

    identity : (a : type) => a -> a = [| _ => x -> x];
    n = identity 5;

Effects
=======

Every expression has an effect row, which is only visible in function types.
Pure expressions have the empty effect row::

    inc : int -! (|) -> int = [| n -> n + 1];

If that is the case the effect annotation can be elided::

    inc : int -> int = [| n -> n + 1];

Side-effecting expressions have non-empty effect rows, e.g. ``println``::

    println : string -! (|io : IO.t|) -> {} =
        [| s -> print (s <> "\n")]

Higher-order functions are often parametric in their effects::

    Array : ARRAY = {
        -- ...

        map : (a, b, e : row) => (a -!e-> b, t a) -!e-> t b
    }

Obviously mapping a function over an array has no effects aside from those from
calling the callback function, which depend on the particular function.

Modules
=======

Modules are blocks that produce records of their bindings instead of the
value of the last expression::

    Point = {
        type t = {|x : int, y : int|};

        fun new x y = {x; y};
        default = new 0 0;
    };

    origin : Point.t = Point.default;

Interfaces
----------

Module interfaces are just the (record) types of module values::

    DEFAULT = {|
        type t;

        default : t;
    |}

Interfaces are essential in providing encapsulation::

    DefaultPoint : DEFAULT = Point;

Here upcasting the ``Point`` module to the ``DEFAULT`` interface hides both the
implementation of the ``Point.t`` type as a record and any associated
operations and values not found in the interface.

Recursive Modules
-----------------

Recursion across module boundaries is supported, even with sealing::

    FILE = {|
        type t;
        size : t -> int;
    |}

    File : FILE = {
        extends enum {
            type t;
            RegularFile : RegularFile.t -> t;
            Directory : Directory.t -> t;
        };

        size = [
            | RegularFile f -> RegularFile.size f
            | Directory d -> Directory.size d
        ];
    };

    RegularFile : FILE = {
        type t = {|name : string; size : int|};

        fun size (f : t) = f.size;
    };

    Directory : FILE = {
        type t = {name : string; files : Array.t File.t};

        fun size ({_ with files}) =
            Array.foldl [| total f -> total + File.size f ]
                        0 files;
    };

Module Functions ('Functors')
-----------------------------

Since we have first-class modules and functions, we also have module functions
(traditionally called 'functors' in ML modules). So we can define generic
abstractions in terms of modules, not just opaque types with no operations::

    ORD = {|
        type t;

        compare : t -> t -> order;
    |};

    ORD_SET = {|
        type t;
        type elem;

        empty : t;
        union : t -> t -> t;
        
        -- ...
    |}

    fun RedBlackSet (Elem : ORD) : ORD_SET where type elem = Elem.t = ...;

Module functions behave 'applicatively' as in OCaml when their bodies are
free of side effects, so this works (unlike in Standard ML)::

    IntSet = RedBlackSet Int;
    IntSet' = RedBlackSet Int;
    s = IntSet.union IntSet.empty IntSet'.empty;

Impure module functions are 'generative' as in Standard ML, creating fresh
types on every call.

Implicits
=========

Implicits can be used to make the type system fill in some values for you::

    ADD = {|
        type t;

        (+) : (t, t) -> t;
    |};

    implicit AddInt = Int;

    (+) : (Add : ADD) => (Add.t, Add.t) -> Add.t
        = [| Add => a b -> Add.+ a b];

    n = 1 + 2; -- Inferred to be `AddInt.+ 1 2`

Implicit functions can also be used to provide more complex inference::

    implicit fun AddVec3D (?Elem : FIELD) = Vec3D Elem
    vec = (Vec3D Int).zero + (Vec3D Int).zero
    -- `vec = (AddVec3D Int).+ (Vec3D Int).zero (Vec3D Int).zero`

Implicits are a general mechanism that can be used for other things as well but
usually we use it like this, to get more inference in generic code instead of
having to write somewhat tedious and verbose module code to perform various
dependency injections.

