***********
Fixpointing
***********

*Symbols* are compile-time/type level strings. The type of a symbol involves
its name:

.. math::

    \mathsf{'foo} : [= "foo"]

The abstract symbol type ``symbol`` is similar to ``type``:

.. math::

    \mathsf{symbol} = \exists \, \sigma : \mathsf{string} \, . \, [= \sigma]

There is a type of first-class forward references::

    FwdRef.t : type -> string -> type

Forward references can be constructed only with symbol literals with names of
in-scope variables e.g. ``FwdRef.ref 'foo``::

    FwdRef.ref : (s : symbol, v : VAR s) => typeof s -> FwdRef.t (varType v) s

.. math::

    \mathsf{FwdRef.ref} : \forall \, \alpha \, (\sigma : \mathsf{string})
        \, . \, ([= \sigma], \mathsf{VAR} \, \alpha \, \sigma)
        \Rightarrow [= \sigma] \rightarrow \mathsf{FwdRef.t} \, \alpha \, \sigma

``VAR`` has to be magical so that it cannot be fooled by user functions e.g.
``{|s : symbol, v : VAR s ? x| ...`` and so that ``FwdRef.ref 'foo`` is
replaced with a reference to an elaborated box such as ``foo__box__42`` by the
recursion checking and elaboration phase. Maybe ``FwdRef.ref`` should just be a
macro instead?

``FwdRef.get`` has the expected type::

    FwdRef.get : (a : type, s : symbol) => FwdRef.t a s -> a

.. math::

    \mathsf{FwdRef.get} : \forall \, \alpha \, (\sigma : \mathsf{string})
        \, . \, ([= \alpha], [= \sigma])
        \Rightarrow \mathsf{FwdRef.t} \, \alpha \, \sigma \rightarrow \alpha

The recursion elaborator only allows forward references to variables outside at
least one fn boundary. This also extends to ``FwdRef.get``. Delayed forward
references may be realized after the definition of the variable, but this only
applies to ``FwdRef``:s with a static variable name. If a function's arguments
involve a ``FwdRef`` it is assumed that the function's return value holds
delayed forward references to the variable of that ``FwdRef``.

Need to prevent use of a statically named ``FwdRef`` for a different binding
with the same name. Alphatization during typechecking (and macroexpansion?!)
should take care of that.

Not sure if this scheme will prevent all premature forward references. The
point is to allow calling functions that only use ``FwdRef`` in ways that
are permitted for regular local forward references.

