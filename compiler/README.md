# Broom Compiler

Written in Standard ML / MLton.

# Dependencies

https://github.com/nilern/nipo is required to build the lexer and parser and
is included as a Git submodule in `../deps/nipo`.

# Building

```sh
> make dev # or
> make prod
```

Just `make` will `make dev`.

# (Integration) Testing

```sh
> make -k itest # -k prevents stopping at the first failed test
```

