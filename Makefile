# -*- makefile-gmake -*-
# To compile with coq 8.3, run "make VERSION=8.3".  That will prevent using unknown command line options.
VERSION = 8.4
ifeq ("$(VERSION)","8.4")
OTHERFLAGS += -indices-matter
# compiling uu0 takes 32 seconds with sharing and 20 seconds with no-sharing, using a patched coq 8.4
OTHERFLAGS += -no-sharing
# OTHERFLAGS += -verbose
else
endif
include Make.makefile

TIME=gnu
ifeq ($(TIME),gnu)
TIMECMD = \time -f "%U sec, %M bytes: $*"
else
ifeq ($(TIME),bsd)
TIMECMD = \time -p
else
ifeq ($(TIME),bash)
TIMECMD = time -p
else
TIMECMD = time
endif
endif
endif
COQC = $(TIMECMD) $(COQBIN)coqc

COQDEFS := --language=none -r '/^[[:space:]]*\(Axiom\|Theorem\|Class\|Instance\|Let\|Ltac\|Definition\|Lemma\|Record\|Remark\|Structure\|Fixpoint\|Fact\|Corollary\|Let\|Inductive\|Coinductive\|Proposition\)[[:space:]]+\([[:alnum:]_]+\)/\2/'
TAGS : $(VFILES); etags $(COQDEFS) $^
clean:clean2
clean2:
	rm -f TAGS
	find . \( -name \*.o -o -name \*.cmi -o  -name \*.cmx -o -name \*.cmxs -o -name \*.native \) -delete
