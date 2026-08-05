COQMF_ARGS = -Q . CantorDiagonal

all: Cantor.vo

Cantor.vo: Cantor.v
	coqc $(COQMF_ARGS) $<

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux .lia.cache .nia.cache

.PHONY: all clean
