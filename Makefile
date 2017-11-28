V=@
.PHONY: plugin install install-plugin clean

# Here is a hack to make $(eval $(shell work
# (copied from coq_makefile generated stuff):
define donewline


endef

includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

all: plugin documentation-check
	$(MAKE) quickChickTool

plugin: Makefile.coq 
	$(MAKE) -f Makefile.coq 

documentation-check: BasicInterface.vo DocumentationCheck.vo

BasicInterface.vo DocumentationCheck.vo: BasicInterface.v DocumentationCheck.v src/QuickChick.vo
	coqc -R src QuickChick -I src BasicInterface.v
	coqc -R src QuickChick -I src DocumentationCheck.v

TEMPFILE := $(shell mktemp)

install: all
	$(V)$(MAKE) -f Makefile.coq install > $(TEMPFILE) || cat $(TEMPFILE)
  # Manually copying the remaining files
#	 $(V)cp src/quickChickLib.cmx $(COQLIB)/user-contrib/QuickChick
#	 $(V)cp src/quickChickLib.o $(COQLIB)/user-contrib/QuickChick
	 $(V)cp src/quickChickTool $(shell echo $(PATH) | tr ':' "\n" | grep opam | uniq)/quickChick

install-plugin:
	$(V)$(MAKE) -f Makefile.coq install > $(TEMPFILE) || cat $(TEMPFILE)

src/quickChickToolLexer.cmo : src/quickChickToolLexer.mll 
	ocamllex src/quickChickToolLexer.mll
	ocamlc -I src -c src/quickChickToolLexer.ml

src/quickChickToolParser.cmo : src/quickChickToolParser.mly
#	menhir --explain src/quickChickToolParser.mly
	ocamlyacc -v src/quickChickToolParser.mly
	ocamlc -I src -c src/quickChickToolParser.mli
	ocamlc -I src -c src/quickChickToolParser.ml

src/%.cmo : src/%.ml
	ocamlc -I src -c $<

quickChickTool: src/quickChickToolTypes.cmo
	$(MAKE) src/quickChickToolParser.cmo
	$(MAKE) src/quickChickToolLexer.cmo
	$(MAKE) src/quickChickTool.cmo
	ocamlc -o src/quickChickTool unix.cma str.cma src/quickChickToolTypes.cmo src/quickChickToolLexer.cmo src/quickChickToolParser.cmo src/quickChickTool.cmo

tests:
	coqc examples/DependentTest.v
	cd examples/ifc-basic; make clean && make
#	cd examples/RedBlack; make clean && make
#	cd examples/stlc; make clean && make


Makefile.coq: _CoqProject
	$(V)coq_makefile -f _CoqProject -o Makefile.coq

clean:
         # This might not work on macs, but then not my problem
	find . -name '*.vo' -print -delete
	find . -name '*.glob' -print -delete
	find . -name *.d -print -delete
	find . -name *.o -print -delete
	find . -name *.cmi -print -delete
	find . -name *.cmx -print -delete
	find . -name *.cmxs -print -delete
	find . -name *.cmo -print -delete
	find . -name *.bak -print -delete
	find . -name *~ -print -delete
	find . -name *.conflicts -print -delete
	find . -name *.output -print -delete
	rm -f Makefile.coq

bc:
	coqwc src/*.v
	coqwc examples/RedBlack/*.v
	coqwc ../ifc/*.v
