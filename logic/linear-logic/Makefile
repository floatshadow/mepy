# Build with the project-local opam switch (./_opam):
#   make          compile all theories
#   make html     generate HTML documentation in ./html
#   make clean
# Every Rocq tool runs through `opam exec`, so no PATH setup is needed.
OPAM_EXEC ?= opam exec --switch=$(CURDIR) --

all: Makefile.rocq
	$(OPAM_EXEC) $(MAKE) -f Makefile.rocq

html: all
	$(OPAM_EXEC) $(MAKE) -f Makefile.rocq html

Makefile.rocq: _RocqProject
	$(OPAM_EXEC) rocq makefile -f _RocqProject -o Makefile.rocq

clean: Makefile.rocq
	$(OPAM_EXEC) $(MAKE) -f Makefile.rocq clean
	rm -rf Makefile.rocq Makefile.rocq.conf html

.PHONY: all html clean
