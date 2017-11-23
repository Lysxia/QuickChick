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

plugin: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq

documentation-check: BasicInterface.vo DocumentationCheck.vo

BasicInterface.vo DocumentationCheck.vo: BasicInterface.v DocumentationCheck.v src/QuickChick.vo
	coqc -R src QuickChick -I src BasicInterface.v
	coqc -R src QuickChick -I src DocumentationCheck.v

TEMPFILE := $(shell mktemp)
OPAM_BIN := $(shell opam config var bin)
OPAM_LIB := $(shell opam config var lib)

install: all install-manual install-plugin

QC_LIB := \
  src/quickchick_lib.a \
  src/quickchick_lib.cmi \
  src/quickchick_lib.cmx \
  src/quickchick_lib.cmxa \
  src/quickchick_lib.cmxs
INSTALL_CMD := ocamlfind install QuickChick
INSTALL_DIR = \
  -destdir $(OPAM_LIB)/coq/user-contrib \
  -metadir $(OPAM_LIB)

# Manually copying the remaining files
install-manual: all src/META $(QC_LIB)
	$(V)cp src/quickChickTool $(OPAM_BIN)/quickChick
	$(V)$(INSTALL_CMD) $(INSTALL_DIR) src/META $(QC_LIB) || $(INSTALL_CMD) -add $(INSTALL_DIR) $(QC_LIB)

uninstall: uninstall-manual
	$(V)rm -rf '$(OPAM_LIB)/coq/user-contrib/QuickChick'

uninstall-manual:
	$(V)rm $(OPAM_BIN)/quickChick
	$(V)ocamlfind remove QuickChick $(INSTALL_DIR)

install-plugin: all
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
	coqc -Q src/ QuickChick examples/DependentTest.v
	$(MAKE) -C examples/ifc-basic
#	cd examples/RedBlack; make clean && make
#	cd examples/stlc; make clean && make


Makefile.coq: _CoqProject
	$(V)coq_makefile -f _CoqProject -o Makefile.coq

Makefile.coq.local: _CoqProject
	$(V)echo 'src/sPRNG.cmx: CAMLPKGS=-package pringo' > Makefile.coq.local

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
	rm -f Makefile.coq Makefile.coq.local

bc:
	coqwc src/*.v
	coqwc examples/RedBlack/*.v
	coqwc ../ifc/*.v
