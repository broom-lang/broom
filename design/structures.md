# Record Types

## Empty

```
{:}
```

## Extend

```
type point = {x : f32, y : f32} # {{:} with x : f32 with y : f32}
type point3d = {point with z : f32}
```

## Update

```
type point64 = {point where x : f64, y : f64} # {point where x : f64 where y : f64}
```

# Records

## Empty

```
{}
```

## Extend

```
val p = {x = 17, y = 23} # {{} with x = 17 with y = 23}
val p3d = {p with z = 0}
```

## Update

```
val p' = {p where x = 42}
```

## Field Access

```
val x = p.x
```

# Record Patterns

## Empty

```
val {} = {}
```

## Extend

```
val {p with z} = p3d # val {p with z = z} = p3d
# p : point, z : f32
```

## Update

```
val {p3d' where z} = p3d # val {p3d' with z = z} = p3d
# p : point3d, z : f32
```

# Interfaces

## Empty

```
type EMPTY = interface end
```

## Extend

```
type ZEROABLE = interface
    type t # val t = type
    val zero : t
end

type BINARYABLE = interface extends Super : ZEROABLE
    val one : Super.t # `with` semantics
end
```

## Update

```
type INT32_ZEROABLE = interface extends ZEROABLE
    override type t = i32
    override val zero : i32
end
```

# Modules

## Empty

```
val Empty = module end
```

## Extend

```
val Int32 = module
    type t = i32 # val t = type i32
    val zero = 0i32
end

val IntOne32 = module extends Super = Int32
    val one = Super.zero + 1 # `with` semantics
end
```

## Update

```
val Int64 = module extends Int32
    override type t = i64 # `where` semantics
    override val one = 0i64
end
```

