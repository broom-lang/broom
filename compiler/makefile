OPAM=opam
EXEC=${OPAM} exec
DUNE=${EXEC} dune --

.PHONY: all
all: build

.PHONY: build
build:
	@${DUNE} build @install

.PHONY: install
install:
	@${OPAM} install ./broom.opam

.PHONY: reinstall
reinstall:
	@${OPAM} reinstall ./broom.opam

.PHONY: uninstall
uninstall:
	@${OPAM} uninstall broom

.PHONY: dev
dev:
	dune build

.PHONY: test
test:
	dune runtest

.PHONY: clean
clean:
	@${DUNE} clean

