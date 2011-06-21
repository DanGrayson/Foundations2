# -*- makefile-gmake -*-
M=Main_Library
P=Proof_of_Extensionality
COQFLAGS = -opt -q
MADE_FILES = 
%.glob %.vo: %.v
	@ echo "make: Entering directory \`$(dir $*)'"
	cd $(dir $*) && coqc $(COQFLAGS) $(notdir $*.v)
	@ echo "make: Leaving directory \`$(dir $*)'"
all:								\
	$M/Generalities/uu0.vo					\
	$M/Generalities/uu1.vo					\
	$M/Generalities/uu1uu0.vo				\
	$P/univ01.vo						\
	$M/hlevel1/hProp.vo					\
	$M/hlevel2/finite_sets.vo				\
	$M/hlevel1/hProp_up.vo					\
	$M/hlevel1/hProp_r.vo					\
	$M/hlevel1/hProp_r_up.vo				\
	$M/hlevel2/hSet_r.vo					\
	$M/hlevel2/hSet_r_up.vo					\
	$M/hlevel2/set_quotients_r_up.vo			\
	$M/hlevel2/set_quotients_constr2_r_up.vo		\
	make-doc

Makefile.depends:
	find . -name \*.v |\
	   >$@ xargs coqdep \
		-I Main_Library/Generalities \
		-I Main_Library/hlevel1 \
		-I Main_Library/hlevel2 \
		-I Proof_of_Extensionality
include Makefile.depends

MADE_FILES += doc
make-doc:
	mkdir -p doc
	cd doc && ( find ../$M ../$P -name \*.v | xargs coqdoc -toc )

.PHONY : uu1
uu1: $M/Generalities/uu1.v
MADE_FILES += $M/Generalities/uu1.v
$M/Generalities/uu1.v: $M/Generalities/uu0.v Makefile uu1.sed
	rm -f $@
	sed <$< >$@ -f uu1.sed
	chmod a-w $@
	head $@

$P/univ01.vo $M/Generalities/uu1uu0.vo: $M/Generalities/uu0.vo $M/Generalities/uu1.vo
clean:
	rm -rf $(MADE_FILES)
	find $M $P \( \
		-name \*.aux -o \
		-name \*.dvi -o \
		-name \*.idx -o \
		-name \*.log -o \
		-name \*.glob -o \
		-name \*.vo -o \
		-name \*.pdf \
		\) -print -delete
