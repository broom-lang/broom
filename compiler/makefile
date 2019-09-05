NIPO = ../deps/nipo/src/nipo
BROOM = broom

.PHONY: dev
dev: $(BROOM)

$(BROOM): main.mlb src/Parser/Lexer.sml src/Parser/Parser.sml \
           $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -const 'Exn.keepHistory true' -output $(BROOM) main.mlb

.PHONY: prod
prod: main.mlb src/Parser/Lexer.sml src/Parser/Parser.sml \
      $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -output $(BROOM) main.mlb

src/Parser/Lexer.sml: src/Parser/lexer.nipo
	$(NIPO) $< > $@

src/Parser/Parser.sml: src/Parser/parser.nipo
	$(NIPO) $< > $@

.PHONY: check
check: main.mlb src/Parser/Lexer.sml src/Parser/Parser.sml \
      $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -stop tc main.mlb

.PHONY: itest
itest: itests
	@echo "All integration tests passed."

.PHONY: itests
itests: $(addsuffix .test, $(basename $(wildcard test/integration/*.brm)))

.PHONY: %.test
%.test: %.brm $(BROOM)
	@expected_err=$(addsuffix .err, $(basename $<)); \
	if [ -f $$expected_err ]; then \
          ./$(BROOM) build --lint $< 2>&1 >/dev/null | diff $$expected_err -; \
        else \
	  ./$(BROOM) build --lint $< 2>&1 | diff /dev/null -; \
        fi

.PHONY: clean
clean:
	rm -rf src/Parser/Lexer.sml src/Parser/Parser.sml $(BROOM)

