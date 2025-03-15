MLTON  = mlton -verbose 0
CP     = cp
RM     = rm

test: *.mlb *.sml
	$(MLTON) -output test sources.mlb

.PHONY: clean
clean:
	$(RM) -rf .cm/
	$(RM) -f test
