NAME=coq-quickchick

V=@
.PHONY: plugin install install-plugin clean quickChickTool quickChickLib
.PHONY: uninstall-qclib

OCAMLBUILD=ocamlbuild -use-ocamlfind

QCTOOL_DIR=quickChickTool
QCTOOL_EXE=quickChickTool.byte
QCTOOL_SRC=$(QCTOOL_DIR)/quickChickTool.ml \
		   $(QCTOOL_DIR)/quickChickToolTypes.ml \
		   $(QCTOOL_DIR)/quickChickToolLexer.mll \
		   $(QCTOOL_DIR)/quickChickToolParser.mly

QCLIB_DIR=quickChickLib
QCLIB_DEPS=-pkg pure-splitmix
QCLIB_TARGETS=quickChickLib.cmxa \
			  quickChickLib.cma \
			  quickChickLib.a
QCLIB_INSTALL_TARGETS = $(addprefix _build/, $(QCLIB_TARGETS))
QCLIB_INSTALL_TARGETS += \
	$(shell find _build/$(QCLIB_DIR)/ \
	-name '*.cmi' -or -name '*.cmo' -or -name '*.o' -or \
	-name '*.mli' -or -name '*.cmx')

# Here is a hack to make $(eval $(shell work
# (copied from coq_makefile generated stuff):
define donewline


endef

includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

all: plugin documentation-check quickChickLib quickChickTool

plugin: Makefile.coq 
	$(MAKE) -f Makefile.coq 

# This dependency forces one ocamlbuild invocation to run at a time.
quickChickLib: quickChickTool
	$(OCAMLBUILD) $(QCLIB_DEPS) -I $(QCLIB_DIR) $(QCLIB_TARGETS)

documentation-check: plugin
	coqc -R src QuickChick -I src BasicInterface.v
	coqc -R src QuickChick -I src DocumentationCheck.v

TEMPFILE := $(shell mktemp)

install: all
	$(V)$(MAKE) -f Makefile.coq install > $(TEMPFILE)
# Manually copying the remaining files
	$(V)cp $(QCTOOL_EXE) $(shell opam config var bin)/quickChick
	ocamlfind install $(NAME) META $(QCLIB_INSTALL_TARGETS)
#	 $(V)cp src/quickChickLib.cmx $(COQLIB)/user-contrib/QuickChick
#	 $(V)cp src/quickChickLib.o $(COQLIB)/user-contrib/QuickChick

install-plugin: Makefile.coq
	$(V)$(MAKE) -f Makefile.coq install | tee $(TEMPFILE)

uninstall:
	$(V)if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq uninstall; fi
	$(RM) $(shell which quickChick | grep opam)

uninstall-qclib:
	ocamlfind remove $(NAME)

src/%.cmo : src/%.ml
	ocamlc -I src -c $<

quickChickTool: $(QCTOOL_EXE)

$(QCTOOL_EXE): $(QCTOOL_SRC)
	ocamlbuild -use-ocamlfind -pkg coq.lib -cflags -rectypes -tag thread $(QCTOOL_DIR)/$(QCTOOL_EXE)

tests:
	cd examples/ifc-basic; make clean && make
	cd examples/RedBlack; make clean && make
	cd examples/stlc; make clean && make
	$(MAKE) -C examples/multifile-mutation test
	$(MAKE) -C examples/c-mutation test
	coqc examples/DependentTest.v

Makefile.coq: _CoqProject
	$(V)coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$Vif [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
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
	find . -name *.aux -print -delete
	rm -f Makefile.coq*

bc:
	coqwc src/*.v
	coqwc examples/RedBlack/*.v
	coqwc ../ifc/*.v
