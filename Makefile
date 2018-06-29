default_target: all

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDOC=$(COQBIN)coqdoc

all: Makefile.coq
	$(MAKE) -f Makefile.coq

doc: all
	$(MAKE) -f Makefile.coq html
html: doc

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq
