#!/bin/bash

function testparser() {
    grammar_etc=$1
    shift
    for parser 
    do python testparser.py -q -nh -w 30 $grammar_etc ${parser//-/ -}
    done 
}

if [ "$1" == "mcfg" ]
then # MCF grammars
    python testparser.py -oh
    testparser '-g abcd.py'          -td  -bu  -td-lc  -bu-lc
    testparser '-g emptygrammar.py'  -td  -bu  -td-lc  -bu-lc  -td-ne  -bu-ne
    testparser '-mcfg -g engaux.mcfg -sf engaux-sentences.txt'         -td  -bu  -td-lc  -bu-lc  -td-ne  -bu-ne
    testparser '-mcfg -g larsonian1.mcfg -sf larsonian-sentences.txt'  -td-lc  -bu-lc  -td-lc-ne  -bu-lc-ne
    testparser '-mcfg -g larsonian2.mcfg -sf larsonian-sentences.txt'  -td-lc  -bu-lc  -td-lc-ne  -bu-lc-ne

elif [ "$1" == "gf" ]
then # GF grammars
    python testparser.py -oh
    testparser '-g AllEngAbs.py -go AllEngAbs -gf AllEng -sf AllEng-sentences.txt -nt 30000'  -td-lc  -bu-lc-ne
    testparser '-g FraCaS.py -go FraCaS -gf FraCaSEng -sf FraCaSEng-sentences.txt -nt 30000 -ns 30'  -td-lc  -bu-lc-ne
    testparser '-g FraCaS.py -go FraCaS -gf FraCaSSwe -sf FraCaSSwe-sentences.txt -nt 30000 -ns 30'  -td-lc  -bu-lc-ne

else
    echo "Usage: $0 (mcfg | gf)"
    exit

fi
