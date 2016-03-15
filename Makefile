ISABELLE=isabelle
ISABELLE_VERSION=Isabelle2016
COMPCERTSSA_FILE=compcertSSA-2.0.tar.gz
COMPCERTSSA_URL="http://compcertssa.gforge.inria.fr/$(COMPCERTSSA_FILE)"
COMPCERTSSA_PATCH=compcertSSA-Braun.patch
COMPCERTSSA_EXTRACTION_PATCH=compcertSSA-extraction-Braun.patch
COMPCERTSSA_TARGET=ia32-linux

.PHONY: clean all compcertSSA FormalSSA ifplot ccomp

all: compcertSSA/midend/SSA/BraunSSA.ml

$(COMPCERTSSA_FILE):
	wget -O $@ $(COMPCERTSSA_URL)

compcertSSA/.patched: $(COMPCERTSSA_FILE)
	tar --exclude=compcertSSA/tools/ndfun.[co]* --exclude=compcertSSA/doc/coq2html.o --exclude=compcertSSA/doc/coq2html.cm[xi] -xzf $(COMPCERTSSA_FILE)
	patch -l -p1 < $(COMPCERTSSA_PATCH)
	touch $@

compcertSSA/midend/SSA/BraunSSA.ml: $(wildcard *.thy) ROOT | compcertSSA/midend/SSA
	@test `$(ISABELLE) getenv -b ISABELLE_IDENTIFIER` = $(ISABELLE_VERSION) || { echo "ERROR: This formalization needs Isabelle2016 to build properly" && exit 1; }
	@test -d `$(ISABELLE) getenv -b AFP` || { echo "ERROR: You need the Archive of Formal Proofs (http://afp.sf.net) installed as an Isabelle component" && exit 1; }
	$(ISABELLE) build -c -d '$$AFP' -d . compcertSSA

compcertSSA/midend/SSA/ExternSSAgen.ml: compcertSSA/.patched

compcertSSA/midend/SSA:
	mkdir -p $@

compcertSSA/Makefile.config: compcertSSA/.patched
	cd compcertSSA;	./configure $(COMPCERTSSA_TARGET)

compcertSSA/extraction/.patched: compcertSSA/Makefile.config
	$(MAKE) -j extraction -C compcertSSA
	patch -l -p1 < $(COMPCERTSSA_EXTRACTION_PATCH)
	touch $@

compcertSSA/ccomp: compcertSSA/extraction/.patched compcertSSA/midend/SSA/ExternSSAgen.ml compcertSSA/midend/SSA/BraunSSA.ml
	$(MAKE) -C compcertSSA
	touch $@

test/ifgen: test/ifgen.c
	$(CC) -O2 -o $@ -std=c99 test/ifgen.c

ifplot: compcertSSA/ccomp test/ifplot.sh test/ifplot.gp test/ifgen
	seq 10 10 1000 | test/ifplot.sh
	gnuplot -p test/ifplot.gp


compcertSSA: compcertSSA/.patched
FormalSSA: compcertSSA/midend/SSA/BraunSSA.ml
ccomp: compcertSSA/ccomp

clean:
	rm -rf compcertSSA
	rm -f ifplot.data
	rm -f test/ifgen
	rm -f if.o
	rm -f $(COMPCERTSSA_FILE)
	isabelle build -c -n -d '$$AFP' -d . compcertSSA ||:
