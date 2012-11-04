
# import pyximport
# pyximport.install(pyimport=True)
# # pyximport.install()
# # import MCFParserC as MCFParser

import MCFParser

import itertools 
import re
import os.path
import GF

GRAMMAR_OBJECT = "grammar"
SENTENCES_OBJECT = "sentences"

def testparser(grammar_file, grammar_object, gf_language, start, # grammar
               sentences, sentences_object, sentences_file, # sentences
               statistics, encoding, nr_trees, nr_sentences, seconds,
               width, no_header, only_header, verbose, quiet, 
               **strategy):

    table_header = (" OK? | Grammar    | Parser   |  Nr |  Len |   Chart | (rul,act,pas,pred) |"
                    "        Time |   Time/item |  Trees | Unique | Correct | Sentence \n"
                    "----:|------------|----------|----:|-----:|--------:|:------------------:|"
                    "------------:|------------:|-------:|-------:|--------:|----------------")
    if only_header:
        print table_header
        return

    assert grammar_file
    assert not (strategy['topdown'] and strategy['bottomup'])
    assert not (gf_language and not grammar_object)
    assert not (statistics and (sentences_object or sentences_file or sentences))
    if not (strategy['topdown'] or strategy['bottomup']):
        strategy['topdown'] = True

    starters = None
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
        if isinstance(grammar, dict):
            grammar = [(f,c,a,r) for (f,(c,a,r)) in grammar.iteritems()]
    if not starters:
        if not start:
            start = grammar[0][1]
        starters = [start]

    if not statistics:
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
    if quiet:
        ctr = MCFParser.TracedCounter("Reading grammar '%s':" % grammar_name)
    parser = MCFParser.Parser(grammar, starters, trace=not quiet, **strategy)
    if quiet:
        ctr.finalize()

    if statistics:
        parser.print_grammar_statistics()
        return

    if not no_header:
        if not quiet:
            header = "%s, %d sentences: %s = %s" % (grammar_file, len(sentences), 
                                                    ", ".join(key for key in strategy if strategy[key]), parser_name)
            print header
            print "=" * len(header)
            print
        print table_header

    if seconds:
        time_multiplier = 1.0
        time_suffix = "s"
    else:
        time_multiplier = 1e3
        time_suffix = "ms"

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
        try: 
            pct_actives = 100.0 * stat['Chart']['Active'] / chartsize
            pct_found = 100.0 * stat['Chart']['Found'] / chartsize
            pct_predicts = 100.0 * stat['Chart']['Symbol'] / chartsize
            pct_dynrules = 100.0 * stat['Chart']['Rule'] / chartsize
            item_time = time / chartsize
        except ZeroDivisionError:
            pct_actives = pct_found = pct_predicts = pct_dynrules = item_time = 0.0
        all_parsed_trees = list(itertools.islice(parser.extract_trees(), nr_trees))
        parsed_trees = len(all_parsed_trees)
        unique_trees = len(set(all_parsed_trees))
        totaltime += time
        totalsize += chartsize
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
            print ('%4s | %-10s | %-8s |%4d |%5d |%8d | (%3.0f,%3.0f,%3.0f,%3.0f%%) | '
                   '%8.2f %-2s | %8.2f us |%7s |%7s | %7s | "%s"' % 
                   ("FAIL" if fail else "", grammar_name[:10], parser_name, n, len(sent), 
                    chartsize, pct_dynrules, pct_actives, pct_found, pct_predicts,
                    time_multiplier*time, time_suffix, 1e6*item_time, parsed_trees, unique_trees, correct_trees, sentstr))
    if quiet: 
        ctr.finalize()
    print ("%4s | %-10s | %-8s |%4d |      |%8d |                    | "
           "%8.2f %-2s | %8.2f us |%7s |%7s | %7s | " % 
           ("FAIL" if totalfail else " OK ", grammar_name[:10], parser_name, len(sentences), 
            1.0*totalsize/len(sentences), 
            time_multiplier*totaltime/len(sentences), time_suffix, 1e6*totaltime/totalsize, 
            total_parsed_trees, total_unique_trees, total_correct_trees))


######################################################################


if __name__ == '__main__':
    import argparse
    argparser = argparse.ArgumentParser()

    topgroup = argparser.add_mutually_exclusive_group(required=True)
    topgroup.add_argument("-oh", "--only-header", action="store_true",  help="print the header line(s) and then quit")
    topgroup.add_argument("-g", "--grammar-file",            help="the Python grammar file")

    grammar_group = argparser.add_argument_group("grammar")
    subgroup = grammar_group.add_mutually_exclusive_group()
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

    statistics_group = argparser.add_argument_group("grammar statistics")
    statistics_group.add_argument("-stat", "--statistics", action="store_true", help="print grammar statistics")

    options_group = argparser.add_argument_group("optional arguments")
    options_group.add_argument("-e", "--encoding", default="utf-8",         help="text encoding (default: 'utf-8')")
    options_group.add_argument("-nt", "--nr-trees", type=int, default=1000, help="max nr. of parse trees (default 1000)")
    options_group.add_argument("-ns", "--nr-sentences", type=int,           help="nr. of sentences to parse")
    options_group.add_argument("-w", "--width", type=int,                   help="max width of text table")
    options_group.add_argument("-sec", "--seconds", action="store_true",    help="show time in seconds instead of milliseconds")
    subgroup = sentence_group.add_mutually_exclusive_group()
    subgroup.add_argument("-nh", "--no-header", action="store_true",    help="don't print the header line(s)")

    subgroup = options_group.add_mutually_exclusive_group()
    subgroup.add_argument("-v", "--verbose", action="store_true")
    subgroup.add_argument("-q", "--quiet", action="store_true")

    args = argparser.parse_args()
    testparser(**vars(args))


