
.PHONY: build test fmt check examples diagram
build:
	dune build
test:
	dune runtest
fmt:
	dune fmt 
check: build test examples
	dune build @fmt
examples: build
	./scripts/check-examples.sh
diagram: build
	dune exec pratty diagram > grammar.html
