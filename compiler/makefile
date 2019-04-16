BROOMC = broomc

.PHONY: dev
dev: $(BROOMC)

$(BROOMC): src/Parser/lexer.x.sml src/Parser/parser.y.sml src/Parser/parser.y.sig \
           $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -const 'Exn.keepHistory true' -output $(BROOMC) main.mlb

.PHONY: prod
prod: src/Parser/lexer.x.sml src/Parser/parser.y.sml src/Parser/parser.y.sig \
      $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -output $(BROOMC) main.mlb

src/Parser/lexer.x.sml: src/Parser/lexer.x
	mllex $^

src/Parser/parser.y.sml: src/Parser/parser.y
	mlyacc $^

src/Parser/parser.y.sig: src/Parser/parser.y
	mlyacc $^

.PHONY: itest
itest: itests
	@echo "All integration tests succeeded."

.PHONY: itests
itests: $(addsuffix .test, $(basename $(wildcard test/integration/*.ml)))

.PHONY: %.test
%.test: %.ml $(BROOMC)
	@expected_err=$(addsuffix .err, $(basename $<)); \
	if [ -f $$expected_err ]; then \
          ./$(BROOMC) <$< 2>&1 >/dev/null | diff $$expected_err -; \
        else \
	  ./$(BROOMC) <$< 2>&1 | diff /dev/null -; \
        fi

.PHONY: clean
clean:
	rm -rf src/Parser/lexer.x.sml src/Parser/parser.y.* $(BROOMC)

