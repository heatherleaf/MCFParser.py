
.DELETE_ON_ERROR:

.PHONY: help clean

ALLGRAMMARS=abcd emptygrammar engaux larsonian1 larsonian2 FraCaSEng FraCaSSwe AllEng
ALLPARSERS=-bu -td -bu-ne -td-ne -bu-lc -td-lc -bu-lc-ne -td-lc-ne

PARSERS?=$(ALLPARSERS)

help:
	@echo "make {grammar}.test PARSERS=..."
	@echo "  where"
	@echo "    {grammar} is one of: $(ALLGRAMMARS)"
	@echo "    ... is one or more of: $(ALLPARSERS)"
	@echo "                           (default is all of them)"

clean:
	rm *.test

%.test: %.py
	./unittest.sh $* $(PARSERS) > $@

AllEng.test: AllEngAbs.py
	./unittest.sh AllEng $(PARSERS) > $@

FraCaS%.test: FraCaS.py
	./unittest.sh FraCaS$* $(PARSERS) > $@

%.py: %.pgf
	gf -make -f python $<

%.py: %.mcfg
	python convert_mcfg_to_py.py $< > $@
