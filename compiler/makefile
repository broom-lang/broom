DESTDIR = /
PREFIX = usr/local/
OPAM=opam
EXEC=${OPAM} exec
DUNE=${EXEC} dune --
BROOM=_build/default/bin/broom.exe

.PHONY: all
all: build

.PHONY: build
build: deps
	${DUNE} build -p broom

.PHONY: deps
deps:
	${OPAM} install --deps-only -y ./broom.opam

.PHONY: install
install: build
	mkdir -p $(DESTDIR)$(PREFIX)bin/; \
	cp $(BROOM) $(DESTDIR)$(PREFIX)bin/broom

.PHONY: uninstall
uninstall:
	rm -f $(DESTDIR)$(PREFIX)bin/broom

.PHONY: dev
dev:
	dune build

.PHONY: test
test:
	dune runtest

.PHONY: clean
clean:
	${DUNE} clean

