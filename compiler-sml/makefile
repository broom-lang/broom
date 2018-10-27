BROOMC = broomc

.PHONY: prod
prod: src/lexer.x.sml src/parser.y.sml src/parser.y.sig \
      $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlton -output $(BROOMC) main.mlb

.PHONY: dev
dev: mlyacc-lib \
     src/lexer.x.sml src/parser.y.sml src/parser.y.sig \
     $(shell find src -name '*.sml' -or -name '*.fun' -or -name '*.sig')
	mlkit -o $(BROOMC) main-dev.mlb

mlyacc-lib:
	cp -R /usr/lib/mlton/sml/mlyacc-lib mlyacc-lib

src/lexer.x.sml: src/lexer.x
	mllex $^

src/parser.y.sml: src/parser.y
	mlyacc $^

src/parser.y.sig: src/parser.y
	mlyacc $^

.PHONY: clean
clean:
	rm -rf mlyacc-lib MLB mlyacc/MLB src/MLB src/lexer.x.sml src/parser.y.* $(BROOMC)
