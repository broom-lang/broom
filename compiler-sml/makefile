BROOMC = broomc

.PHONY: dev
dev: src/lexer.x.sml src/parser.y.sml src/parser.y.sig \
      $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -const 'Exn.keepHistory true' -output $(BROOMC) main.mlb

.PHONY: prod
prod: src/lexer.x.sml src/parser.y.sml src/parser.y.sig \
      $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -output $(BROOMC) main.mlb

src/lexer.x.sml: src/lexer.x
	mllex $^

src/parser.y.sml: src/parser.y
	mlyacc $^

src/parser.y.sig: src/parser.y
	mlyacc $^

.PHONY: clean
clean:
	rm -rf src/lexer.x.sml src/parser.y.* $(BROOMC)
