# Introduction to Broom

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

(With types `where` has a more specialized function.)

Record fields can be read with the familiar dot notation:

```
val x: int = point'.x # = 42
```

