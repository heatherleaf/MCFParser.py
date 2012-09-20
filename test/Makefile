
GF-DIR = ~/Projekt/GF

GF-MAKE = gf -make -optimize-pgf -f python

.PHONY: help test clean

help:
	@echo "make (mcfg | gf)"

mcfg gf: 
	@./unittest.sh $@

gf: AllEngAbs.py FraCaS.py


FRACAS-DIR = $(GF-DIR)/examples/fracas/src

FraCaS.py: $(FRACAS-DIR)/FraCaSEng.gf $(FRACAS-DIR)/FraCaSSwe.gf
	$(GF-MAKE) $^

AllEngAbs.py: 
	$(GF-MAKE) alltenses/AllEng.gfo
