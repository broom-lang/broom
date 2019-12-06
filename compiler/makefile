BROOM = broom 
.PHONY: dev
dev: $(BROOM)

$(BROOM): main.mlb src/Parser/parser.ml-antlr.sml src/Parser/lexer.ml-ulex.sml \
           $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -const 'Exn.keepHistory true' -output $(BROOM) main.mlb

.PHONY: prod
prod: main.mlb src/Parser/parser.ml-antlr.sml src/Parser/lexer.ml-ulex.sml \
      $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -output $(BROOM) main.mlb

.PHONY: check
check: main.mlb src/Parser/parser.ml-antlr.sml src/Parser/lexer.ml-ulex.sml \
      $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -stop tc main.mlb

%.ml-antlr.sml: %.ml-antlr
	ml-antlr $<

%.ml-ulex.sml: %.ml-ulex
	ml-ulex --strict-sml $<

.PHONY: utest
utest: $(shell find test/unit -name '*.sml' -or -name '*.mlb')
	mlton -const 'Exn.keepHistory true' test/unit/unit.mlb && ./test/unit/unit

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

.PHONY: clean
clean:
	rm -rf src/Parser/parser.ml-antlr.sml src/Parser/lexer.ml-ulex.sml $(BROOM)

