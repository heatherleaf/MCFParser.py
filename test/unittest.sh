#!/bin/bash

maxtrees=10000
nrsentences=30

GFgrammars="AllEng FraCaSEng FraCaSSwe"

testcmd="python testparser.py -q -nh -w 30 -nt $maxtrees -ns $nrsentences"

parsers="-bu -td -bu-ne -td-ne -bu-lc -td-lc -bu-lc-ne -td-lc-ne"

if [ $# -eq 0 ]; then
    echo "Usage: $0 grammar [$parsers]" 1>&2
    exit 1
fi

grammar=$1
shift

sentences=$grammar-sentences.txt

# GF grammars
case "$grammar" in
    AllEng)    gfbase=AllEngAbs ;;
    FraCaSEng) gfbase=FraCaS    ;;
    FraCaSSwe) gfbase=FraCaS    ;;
esac
if [ -n "$gfbase" ]; then
    testcmd="$testcmd -gf $grammar -go $gfbase"
    grammar=$gfbase
fi

if ! [ -f "$grammar.py" ]; then
    echo "Grammar does not exist: $grammar.py" 1>&2
    exit 1
fi
testcmd="$testcmd -g $grammar.py"

echo "################################################################################"
echo "## Testing grammar: $grammar"
echo "## $testcmd"
echo
echo "## Original grammar"
echo
$testcmd -stat -td -lc
echo
echo "## Nonempty grammar"
echo
$testcmd -stat -td -lc -ne
echo

if [ $# -eq 0 ]; then
    echo "Provide one or more of [$parsers] to test the parsers" 1>&2
    exit
fi

if [ -f "$sentences" ]; then
    testcmd="$testcmd -sf $sentences"
fi

echo "## Testing the parsers"
echo
python testparser.py -oh
for parser in "$@"; do
    $testcmd ${parser//-/ -}
done
