
.PHONY: all clean

all: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.coq.local:
	echo ".PHONY: Driver.vo" > Makefile.coq.local
