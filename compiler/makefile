BROOMC = broomc

.PHONY: dev
dev: src/Parser/lexer.x.sml src/Parser/parser.y.sml src/Parser/parser.y.sig \
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
itest: $(addsuffix .test, $(basename $(wildcard test/integration/*.ml)))

.PHONY: %.itest
%.test: %.ml dev
	./$(BROOMC) <$< | diff /dev/null -

.PHONY: clean
clean:
	rm -rf src/Parser/lexer.x.sml src/Parser/parser.y.* $(BROOMC)

