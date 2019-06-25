BROOM = broom

.PHONY: dev
dev: $(BROOM)

$(BROOM): main.mlb src/Parser/lexer.x.sml src/Parser/parser.y.sml src/Parser/parser.y.sig \
           $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -const 'Exn.keepHistory true' -output $(BROOM) main.mlb

.PHONY: prod
prod: src/Parser/lexer.x.sml src/Parser/parser.y.sml src/Parser/parser.y.sig \
      $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -output $(BROOM) main.mlb

src/Parser/lexer.x.sml: src/Parser/lexer.x
	mllex $^

src/Parser/parser.y.sml: src/Parser/parser.y
	mlyacc $^

src/Parser/parser.y.sig: src/Parser/parser.y
	mlyacc $^

.PHONY: itest
itest: itests
	@echo "All integration tests passed."

.PHONY: itests
itests: $(addsuffix .test, $(basename $(wildcard test/integration/*.ml)))

.PHONY: %.test
%.test: %.ml $(BROOM)
	@expected_err=$(addsuffix .err, $(basename $<)); \
	if [ -f $$expected_err ]; then \
          ./$(BROOM) build --lint $< 2>&1 >/dev/null | diff $$expected_err -; \
        else \
	  ./$(BROOM) build --lint $< 2>&1 | diff /dev/null -; \
        fi

.PHONY: clean
clean:
	rm -rf src/Parser/lexer.x.sml src/Parser/parser.y.* $(BROOM)

