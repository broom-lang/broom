BROOM = broom
BROOM_HEAP = broom.amd64-linux
SMLNJ_HOME = /usr/lib/smlnj

# Production build of compiler via MLton:
.PHONY: prod
prod: main.mlb src/Parser/parser.ml-antlr.sml src/Parser/lexer.ml-ulex.sml \
      $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -output $(BROOM) main.mlb

# Development build of compiler via MLton with debug options:
.PHONY: dev
dev: $(BROOM)

$(BROOM): main.mlb src/Parser/parser.ml-antlr.sml src/Parser/lexer.ml-ulex.sml \
     $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -const 'Exn.keepHistory true' -output $(BROOM) main.mlb

# SML/NJ heap that can be loaded with `sml @SMLload=...` (`heap2exec` did not work):
.PHONY: smlnj-heap
smlnj-heap: $(BROOM_HEAP)

$(BROOM_HEAP): main.cm src/Parser/parser.ml-antlr.sml src/Parser/lexer.ml-ulex.sml \
               $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	SMLNJ_HOME=$(SMLNJ_HOME) ml-build -Cparser.succ-ml=true main.cm Main.main $(BROOM)

# Just typecheck everything (via MLton):
.PHONY: check
check: main.mlb src/Parser/parser.ml-antlr.sml src/Parser/lexer.ml-ulex.sml \
      $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -stop tc main.mlb

# Generate ml-ulex lexer:
%.ml-ulex.sml: %.ml-ulex
	ml-ulex --strict-sml $<

# Generate ml-antlr parser:
%.ml-antlr.sml: %.ml-antlr
	ml-antlr $<

# Run unit tests:
.PHONY: utest
utest: $(shell find test/unit -name '*.sml' -or -name '*.mlb')
	mlton -const 'Exn.keepHistory true' test/unit/unit.mlb && ./test/unit/unit

# Run integration tests:
.PHONY: itest
itest: itests
	@echo "All integration tests passed."

.PHONY: itests
itests: $(addsuffix .test, $(basename $(wildcard test/integration/*.brm)))

.PHONY: %.test
%.test: %.brm $(BROOM)
	@expected_err=$(addsuffix .err, $(basename $<)); \
	if [ -f $$expected_err ]; then \
          ./$(BROOM) build $< 2>&1 >/dev/null | diff $$expected_err -; \
        else \
	  ./$(BROOM) build --lint $< 2>&1 | diff /dev/null -; \
        fi

# Remove generated files:
.PHONY: clean
clean:
	rm -rf src/Parser/parser.ml-antlr.sml src/Parser/lexer.ml-ulex.sml $(BROOM) $(BROOM_HEAP)

