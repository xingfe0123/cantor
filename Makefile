COQMF_ARGS = -Q . CantorDiagonal

all: Cantor.vo

Cantor.vo: Cantor.v
	coqc $(COQMF_ARGS) $<

check: Cantor.vo
	echo 'From CantorDiagonal Require Import Cantor.' > /tmp/_check.v
	echo 'Print Assumptions seq01_uncountable.' >> /tmp/_check.v
	echo 'Print Assumptions no_surjection_general.' >> /tmp/_check.v
	echo 'Print Assumptions diagonal_not_in_range.' >> /tmp/_check.v
	rocq compile $(COQMF_ARGS) /tmp/_check.v
	rm -f /tmp/_check.v /tmp/_check.vo /tmp/_check.vos /tmp/_check.vok /tmp/_check.glob /tmp/._check.aux

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux .lia.cache .nia.cache

.PHONY: all clean check
