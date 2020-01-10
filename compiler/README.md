# Broom Compiler

Written in Standard ML (with Successor ML extensions).

# Dependencies

You need an SML compiler and the ml-lpt tools `ml-ulex` and `ml-antlr`. You get
both by installing SML/NJ. We use MLton for production builds as it makes
standalone executables easier (and smaller and faster). Unfortunately MLton
does not come with the ml-lpt binaries so you have to install SML/NJ anyway.

# Building

```sh
> make smlnj-dev # or
> make dev # or
> make prod
```

Just `make` will `make smlnj-dev`. That will create an SML/NJ heap image that
can be run with `sml @SMLload=broom.amd64-linux ...`. The other options use
MLton to create a `broom` binary.

# (Integration) Testing

```sh
> make -k itest # -k prevents stopping at the first failed test
```

