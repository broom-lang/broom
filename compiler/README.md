# Broom Compiler

Written in Standard ML / MLton.

# Dependencies

In addition to MLton, the ml-lpt tools `ml-ulex` and `ml-antlr` are required to
build. The easiest way to obtain thoMLton has other virtues to make up for not coming with ml-lpt).
in addition to MLton! We do have an issue for building with just SML/NJ, but
MLton has other virtues to make up for not coming with ml-lpt).

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

