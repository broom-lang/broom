# Interface Operations

```
# Literal:
type TYP = interface type t end
type INT_TYP = interface type t = int end

# Inheritance:
type DEFAULT = interface extends TYP
    default: t # Inheritance is nasty but how else can we do this?
end

# Refinement:
type INT_DEFAULT = {DEFAULT where type t = int} # Ambiguous (expr or type?)

# Extension:
type INT_MONOID = {INT_DEFAULT with mappend: int -> int}
```

# Module Operations

```
# Literal:
IntTyp: INT_TYP = module type t = int end

# Inheritance:
IntDefault: INT_DEFAULT = module extends IntTyp
    default: t = 0 # Unlike interfaces, we could do without inheritance by `default: IntTyp.t`
    # `override` could be used to get the `where` instead of `with` semantics on a given field.
end

# Extension:
IntAddMonoid: INT_MONOID = {IntDefault with mappend = (+)}

# Refinement (overwrite of functional update):
IntMulMonoid: INT_MONOID = {IntAddMonoid where default <- (+ 1), mappend = (*)}

# Selection:
zero = IntAddMonoid.mappend IntAddMonoid.default IntAddMonoid.default
one = IntMulMonoid.mappend IntMulMonoid.default IntMulMonoid.default
```

# Record Types and Values

```
empty: {:} = {}

point: {x: int, y: int} = {empty with x = 5, y = 8}

# Row polymorphism:
getX: forall a (r \ x) => {r with x: a} -> a = {|r -> r.x}
dropX: forall a (r \ x) => {r with x: a} -> {r} = {|r -> }
```

