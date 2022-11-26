DESTDIR = /
PREFIX = usr/local/
BROOM = broom
RUNTIME = libbroom_runtime.a

# Build both compiler and runtime:
.PHONY: all
all: compiler runtime

# Build (production) compiler:
.PHONY: compiler
compiler:
	cd compiler; \
        make prod && cp $(BROOM) ../

# Build (production) runtime:
.PHONY: runtime
runtime:
	cd runtime/gc; \
        cargo build --release && cp target/release/$(RUNTIME) ../../

# Remove generated files:
.PHONY: clean
clean:
	cd compiler; make clean; cd ..; \
	cd runtime/gc; cargo clean; cd ../..; \
        rm -f $(BROOM) $(RUNTIME)

# Install compiler and runtime to filesystem:
.PHONY: install
install: $(BROOM) $(RUNTIME)
	mkdir -p $(DESTDIR)$(PREFIX)bin/; \
	cp $(BROOM) $(DESTDIR)$(PREFIX)bin/$(BROOM); \
	mkdir -p $(DESTDIR)$(PREFIX)lib/broom; \
        cp $(RUNTIME) $(DESTDIR)$(PREFIX)lib/broom/

# Uninstall compiler and runtime from filesystem:
.PHONY: uninstall
uninstall:
	rm -f $(DESTDIR)$(PREFIX)bin/$(BROOM) $(DESTDIR)$(PREFIX)lib/broom/$(RUNTIME); \
        rmdir $(DESTDIR)$(PREFIX)lib/broom

