DESTDIR = /
PREFIX = usr/local/
BROOM=_build/default/bin/broom.exe

.PHONY: all
all: build

.PHONY: build
build: deps
	dune build --profile release

.PHONY: deps
deps:
	opam install --deps-only -y ./broom.opam

.PHONY: install
install: build
	mkdir -p $(DESTDIR)$(PREFIX)bin/; \
	cp $(BROOM) $(DESTDIR)$(PREFIX)bin/broom; \
	chmod 755 $(DESTDIR)$(PREFIX)bin/broom; \
	strip $(DESTDIR)$(PREFIX)bin/broom; \
	chmod 555 $(DESTDIR)$(PREFIX)bin/broom

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
	dune clean

