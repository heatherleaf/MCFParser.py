#!/bin/bash

PYTHON=python

function testparser() {
    grammar_etc=$1
    shift
    for parser 
    do $PYTHON testparser.py -q -nh -w 30 $grammar_etc ${parser//-/ -}
    done 
}

if [ "$1" == "mcfg" ]
then # MCF grammars
    echo
    echo "## Original grammar"
    echo
    $PYTHON testparser.py -q -nh -g larsonian1.py -stat -td -lc
    echo
    echo "## Nonempty grammar"
    echo
    $PYTHON testparser.py -q -nh -g larsonian1.py -stat -td -lc -ne
    echo
    $PYTHON testparser.py -oh
    testparser '-g emptygrammar.py'  -td  -bu  -td-lc  -bu-lc  -td-ne  -bu-ne
    testparser '-g larsonian1.py'  -td  -td-ne  -td-lc  -bu-lc  -td-lc-ne  -bu-lc-ne
    # testparser '-g larsonian2.py'  -td  -bu  -td-ne  -bu-ne  -td-lc  -bu-lc  -td-lc-ne  -bu-lc-ne

elif [ "$1" == "gf" ]
then # GF grammars
    # echo
    # echo "## Original grammar"
    # echo
    # $PYTHON testparser.py -q -nh -g FraCaS.py -go FraCaS -gf FraCaSEng -stat -td -lc
    # echo
    # echo "## Nonempty grammar"
    # echo
    # $PYTHON testparser.py -q -nh -g FraCaS.py -go FraCaS -gf FraCaSEng -stat -td -lc -ne
    # echo
    $PYTHON testparser.py -oh
    # testparser '-g FraCaS.py -go FraCaS -gf FraCaSEng -sf FraCaSEng-sentences.txt -nt 30000 -ns 100'  -td-lc-ne -bu-lc -td-ne   -bu
    testparser '-g AllEngAbs.py -go AllEngAbs -gf AllEng -sf AllEng-sentences.txt -nt 30000'  -td-lc 
    # testparser '-g FraCaS.py -go FraCaS -gf FraCaSEng -sf FraCaSEng-sentences.txt -nt 30000 -ns 30'  -td-lc  -bu-lc-ne
    # testparser '-g FraCaS.py -go FraCaS -gf FraCaSSwe -sf FraCaSSwe-sentences.txt -nt 30000 -ns 30'  -td-lc  -bu-lc-ne

else
    echo "Usage: $0 (mcfg | gf)"
    exit

fi
