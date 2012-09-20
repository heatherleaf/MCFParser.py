
import itertools 
import re
import os.path
import GF
import MCFParser

GRAMMAR_OBJECT = "grammar"
SENTENCES_OBJECT = "sentences"

def testparser(grammar_file, mcfg, grammar_object, gf_language, start, # grammar
               sentences, sentences_object, sentences_file, # sentences
               encoding, nr_trees, nr_sentences, width, no_header, only_header, verbose, quiet,
               **strategy):

    if not no_header:
        print (" OK? | Grammar    | Parser   |  Nr |  Len |   Chart | (rul,act,pas,pred) | Inf.ces |   (+%) |"
               "        Time |   Time/item |  Trees | Unique | Correct | Sentence")
        print ("----:|------------|----------|----:|-----:|--------:|:------------------:|--------:|:------:|"
               "------------:|------------:|-------:|-------:|--------:|----------------")
    if only_header:
        return

    assert grammar_file
    assert strategy['topdown'] or strategy['bottomup']
    assert not (gf_language and not grammar_object)
    assert not (mcfg and grammar_object)
    assert not (mcfg and sentences_object)
    assert not (mcfg and not sentences and not sentences_file)

    starters = None
    if mcfg:
        with open(grammar_file) as F:
            grammar = read_mcfg_file(F, encoding)
    else:
        grammar_module = {}
        execfile(grammar_file, grammar_module)
        if not grammar_object:
            grammar_object = GRAMMAR_OBJECT
        if gf_language:
            gf_grammar = GF.PGF(grammar_module[grammar_object])[gf_language]
            grammar = gf_grammar.mcfrule_iter()
            if not start:
                starters = gf_grammar.cnccats[gf_grammar.abstract.start]
        else:
            grammar = grammar_module[grammar_object]
    if not starters:
        if not start:
            start = grammar[0][1]
        starters = [start]

    if not sentences:
        if sentences_file:
            sentences = []
            with open(sentences_file) as F:
                for line in F:
                    if encoding: 
                        line = line.decode(encoding).strip()
                    if line:
                        sentences.append(line)
        else:
            if not sentences_object:
                sentences_object = SENTENCES_OBJECT
            sentences = grammar_module[sentences_object]

    def convert_sentence(s):
        if isinstance(s, basestring) and ":" in s:
            s = tuple(s.split(":", 1))
        if isinstance(s, tuple) and len(s) == 2:
            n, s = s
            n = int(n)
        else:
            n = -1
        if isinstance(s, basestring):
            s = s.split()
        return n, s

    if nr_sentences > 0:
        sentences = sentences[:nr_sentences]
    sentences = map(convert_sentence, sentences)

    grammar_name = gf_language or grammar_file
    grammar_name = os.path.splitext(os.path.basename(grammar_name))[0]
    parser_name = ""
    if strategy["topdown"]: parser_name += "td"
    if strategy["bottomup"]: parser_name += "bu"
    if strategy["filtered"]: parser_name += "-lc"
    if strategy["nonempty"]: parser_name += "-ne"
    if not quiet:
        header = "%s, %d sentences: %s = %s" % (grammar_file, len(sentences), 
                                                ", ".join(key for key in strategy if strategy[key]), parser_name)
        print header
        print "=" * len(header)
        print
    if quiet:
        ctr = MCFParser.TracedCounter("Reading grammar '%s':" % grammar_name)
    parser = MCFParser.Parser(grammar, starters, trace=not quiet, **strategy)
    if quiet:
        ctr.finalize()

    if quiet:
        ctr = MCFParser.TracedCounter("Parsing:", interval=1)
    totaltime = totalsize = totalincfs = total_parsed_trees = total_unique_trees = total_correct_trees = 0
    totalfail = False
    for n, (correct_trees, sent) in enumerate(sentences, 1):
        if correct_trees > nr_trees: 
            correct_trees = nr_trees
        result = parser.chart_parse(sent, trace=int(verbose))
        stat = parser.statistics
        time = stat['Time']
        chartsize = stat['Chart']['TOTAL']
        inferences = stat['Inferences']['TOTAL']
        try: 
            pct_actives = 100.0 * stat['Chart']['Active'] / chartsize
            pct_found = 100.0 * stat['Chart']['Found'] / chartsize
            pct_predicts = 100.0 * stat['Chart']['Symbol'] / chartsize
            pct_dynrules = 100.0 * stat['Chart']['Rule'] / chartsize
            pct_inferences = 100.0 * (inferences-chartsize) / chartsize
            item_time = time / chartsize
        except ZeroDivisionError:
            pct_actives = pct_found = pct_predicts = pct_dynrules = pct_inferences = item_time = 0.0
        all_parsed_trees = list(itertools.islice(parser.extract_trees(), nr_trees))
        parsed_trees = len(all_parsed_trees)
        unique_trees = len(set(all_parsed_trees))
        totaltime += time
        totalsize += chartsize
        totalincfs += inferences
        total_parsed_trees += parsed_trees
        total_unique_trees += unique_trees
        total_correct_trees += correct_trees if correct_trees >= 0 else parsed_trees
        fail = "F" if bool(result) != bool(parsed_trees) else ""
        if parsed_trees == correct_trees: correct_trees = "" 
        if parsed_trees == unique_trees: unique_trees = ""
        totalfail |= bool(fail or unique_trees or (correct_trees and correct_trees >= 0))
        if parsed_trees == nr_trees: parsed_trees = "%s+" % nr_trees
        sentstr = " ".join(sent)
        if width: sentstr = sentstr[:width]
        if encoding: sentstr = sentstr.encode(encoding)
        if quiet: ctr.inc()
        if not quiet or fail or unique_trees or correct_trees:
            print ('%4s | %-10s | %-8s |%4d |%5d |%8d | (%3.0f,%3.0f,%3.0f,%3.0f%%) |%8d | (%+3.0f%%) | '
                   '%8.2f ms | %8.2f us |%7s |%7s | %7s | "%s"' % 
                   ("FAIL" if fail else "", grammar_name[:10], parser_name, n, len(sent), 
                    chartsize, pct_dynrules, pct_actives, pct_found, pct_predicts,
                    inferences, pct_inferences,
                    1e3*time, 1e6*item_time, parsed_trees, unique_trees, correct_trees, sentstr))
    if quiet: 
        ctr.finalize()
    pct_inferences = 100.0 * (totalincfs - totalsize) / totalsize
    print ("%4s | %-10s | %-8s |%4d |      |%8d |                    |%8d | "
           "(%+3.0f%%) | %8.2f ms | %8.2f us |%7s |%7s | %7s | " % 
           ("FAIL" if totalfail else " OK ", grammar_name[:10], parser_name, len(sentences), 
            1.0*totalsize/len(sentences), 1.0*totalincfs/len(sentences), pct_inferences, 
            1e3*totaltime/len(sentences), 1e6*totaltime/totalsize, 
            total_parsed_trees, total_unique_trees, total_correct_trees))


######################################################################

def read_mcfg_file(file, encoding):
    grammar = []
    for linenr, line in enumerate(file):
        if encoding: 
            line = line.decode(encoding)
        syms = line.split()
        if not mcfg_endofstring(syms):
            try:
                lhs = syms.pop(0)
                rhs = []
                mapping = [[]]
                assert mcfg_nonterminal(lhs)
                assert syms.pop(0).lstrip("-") == ">"
                sym = syms.pop(0)
                if mcfg_empty(sym):
                    assert mcfg_endofstring(syms)
                elif mcfg_terminal(sym):
                    mapping[0].append(mcfg_terminal(sym))
                    while not mcfg_endofstring(syms):
                        sym = mcfg_terminal(syms.pop(0))
                        assert sym
                        mapping[0].append(sym)
                elif mcfg_nonterminal(sym):
                    rhs.append(sym)
                    while mcfg_nonterminal(syms[0]):
                        rhs.append(syms.pop(0))
                    mapping = mcfg_mapping(syms.pop(0))
                    assert mapping and mcfg_endofstring(syms)
                else:
                    assert False
                name = "%s:%s/%d" % (lhs, "+".join(rhs), linenr)
                grammar.append((name, lhs, rhs, mapping))
            except AssertionError, IndexError:
                raise SyntaxError("Unrecognized line nr %d: %s" % (linenr, line))
    return grammar


def mcfg_nonterminal(sym):
    return sym.replace("_","").isalnum() and sym[0].isalpha()

def mcfg_terminal(sym):
    if len(sym) > 2 and sym[0] in "'\"" and sym[0] == sym[-1] and not any(c.isspace() for c in sym):
        return sym[1:-1]
    else:
        return None

def mcfg_empty(sym):
    return sym == "''" or sym == '""'

def mcfg_mapping(sym):
    if re.match(r"(\[ (\d+,\d+ (; \d+,\d+)*)? \])+", sym, flags=re.VERBOSE):
        return [[tuple(int(n) for n in arg.split(","))
                 for arg in row.split(";")]
                for row in sym.strip("][").split("][")]
    else:
        return None

def mcfg_endofstring(syms):
    return not syms or syms[0] in ("(*", "/*")

######################################################################


if __name__ == '__main__':
    import argparse
    argparser = argparse.ArgumentParser()

    grammar_group = argparser.add_argument_group("grammar")
    grammar_group.add_argument("-g", "--grammar-file",            help="the grammar file (.py or .mcfg)")
    subgroup = grammar_group.add_mutually_exclusive_group()
    subgroup.add_argument("-mcfg", "--mcfg", action="store_true", help="the grammar is in MCFG text format")
    subgroup.add_argument("-go", "--grammar-object",              help="name of the Python grammar object (default: '%s')" % GRAMMAR_OBJECT)
    subgroup = grammar_group.add_mutually_exclusive_group()
    subgroup.add_argument("-gf", "--gf-language",           help="the concrete language if the grammar is in GF format")
    subgroup.add_argument("-start", "--start",              help="the start nonterminal (default: inferred from the first rule in the grammar)")

    sentence_group = argparser.add_argument_group("test sentences")
    subgroup = sentence_group.add_mutually_exclusive_group()
    subgroup.add_argument("-so", "--sentences-object",  help="name of the Python list of sentences (default: '%s')" % SENTENCES_OBJECT)
    subgroup.add_argument("-sf", "--sentences-file",    help="text file to read sentences from")
    subgroup.add_argument("-s", "--sentence", action="append", dest="sentences", help="test sentence")

    parser_group = argparser.add_argument_group("parsing algorithm")
    subgroup = parser_group.add_mutually_exclusive_group()
    subgroup.add_argument("-td", "--topdown", action="store_true",      help="use topdown strategy")
    subgroup.add_argument("-bu", "--bottomup", action="store_true",     help="use bottomup strategy")
    parser_group.add_argument("-lc", "--filtered", action="store_true", help="use left-corner filtering")
    parser_group.add_argument("-ne", "--nonempty", action="store_true", help="convert grammar to nonempty format")

    options_group = argparser.add_argument_group("optional arguments")
    options_group.add_argument("-e", "--encoding", default="utf-8",         help="text encoding (default: 'utf-8')")
    options_group.add_argument("-nt", "--nr-trees", type=int, default=1000, help="max nr. of parse trees (default 1000)")
    options_group.add_argument("-ns", "--nr-sentences", type=int,           help="nr. of sentences to parse")
    options_group.add_argument("-w", "--width", type=int,                   help="max width of text table")
    subgroup = sentence_group.add_mutually_exclusive_group()
    subgroup.add_argument("-nh", "--no-header", action="store_true",    help="don't print the header line(s)")
    subgroup.add_argument("-oh", "--only-header", action="store_true",  help="print the header line(s) and then quit")

    subgroup = options_group.add_mutually_exclusive_group()
    subgroup.add_argument("-v", "--verbose", action="store_true")
    subgroup.add_argument("-q", "--quiet", action="store_true")

    args = argparser.parse_args()
    testparser(**vars(args))


