all: Makefile.coq
	$(MAKE) -f Makefile.coq $@
.PHONY: all

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

.DEFAULT: Makefile.coq
	$(MAKE) -f Makefile.coq $@
