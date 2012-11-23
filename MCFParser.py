# -*- coding: utf-8 -*-

# MCFParser.py
# Copyright (C) 2012, Peter Ljunglöf. All rights reserved.

# This file is part of MCFParser.py
#
# MCFParser.py is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or 
# (at your option) any later version.
#
# MCFParser.py is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with MCFParser.py.  If not, see <http://www.gnu.org/licenses/>.


"""
This module contains parsing algorithms for Parallel Multiple 
Context-Free Grammars (PMCFG), as described in:

Peter Ljunglöf (2012). Practical Parsing of Parallel Multiple 
Context-Free Grammars. In Proceedings of TAG+11, the 11th International 
Workshop on Tree Adjoining Grammars and Related Formalisms.
26-28 September, Paris, France.

Since PMCFG includes MCFG and LCFRS, this parser can be used to parse 
these formalisms too. Example usage:

    >>> grammar = [('f', 'S', ['A'], [[(0,0), (0,1)]]),
    ...            ('g', 'A', ['A'], [['a', (0,0), 'b'], ['c', (0,1), 'd']]),
    ...            ('h', 'A', [],    [['a', 'b'], ['c', 'd']])]

    >>> parser = Parser(grammar, ['S'])

    >>> for tree in parser.parse("a a a b b b c c c d d d".split()):
    ...     print tree
    ('f', ('g', ('g', ('h',))))

A grammar can also use string labels, instead of integers:

    >>> grammar = [('f', 'S', ['A'], {'s':[(0,'p'), (0,'q')]}),
    ...            ('g', 'A', ['A'], {'p':['a', (0,'p'), 'b'], 'q':['c', (0,'q'), 'd']}),
    ...            ('h', 'A', [],    {'p':['a', 'b'], 'q':['c', 'd']})]

    >>> list(Parser(grammar, ['S']).parse("a a a b b b c c c d d d".split()))
    [('f', ('g', ('g', ('h',))))]

For more information, try help(Parser).
"""

from collections import defaultdict, namedtuple
import sys
import time
import math

class Parser(object):
    """
    A class for parsing PMCFG/MCFG/LCFRS grammars.

    To create a PMCFG/MCFG/LCFRS parser, you need a sequence of PMCFG 
    grammar rules, and one or several starting nonterminals/categories.

        >>> grammar = [('f', 'S', ['A'], [[(0,0), (0,1)]]),
        ...            ('g', 'A', ['A'], [['a', (0,0), 'b'], ['c', (0,1), 'd']]),
        ...            ('h', 'A', [], [['a', 'b'], ['c', 'd']])]

        >>> parser = Parser(grammar, ['S'], bottomup=True, filtered=True, trace=0)

        >>> for tree in parser.parse("a a b b c c d d".split()):
        ...     print tree
        ('f', ('g', ('h',)))

        >>> parser.chart_parse("a a b b c c d d".split())
        True

        >>> for tree in parser.extract_trees():
        ...     print tree
        ('f', ('g', ('h',)))

        >>> parser.print_grammar_statistics()
        Grammar statistics          ||
        -------------------|--------:|
        Nr. terminals      |       2 |
        Nr. nonterminals   |       2 |
        Nr. nonterm-const. |       3 |
        Nr. grammar rules  |       3 |
        Nr. constituents   |       5 |
        Nr. const. lengths |      12 |
        Nr. empty const.   |       0 |
        Nr. leftc. pairs   |       4 |
        Nr. lcword. pairs  |       2 |

        >>> parser.print_parse_statistics()
        Statistics |    TOTAL |   Active |    Found |     Rule |   Symbol |
        -----------|---------:|---------:|---------:|---------:|---------:|
        Chart      |       31 |       16 |        5 |        5 |        5 |
        Inferences |       31 |       16 |        5 |        5 |        5 |
        Time       |     0.00 |

    The tracing level is used in many methods. These are the possible values:

      - None: No tracing, do not even collect statistics.
      - 0: No tracing, but collect parsing statistics.
      - 1: Print short tracing information to standard error.
      - 2: Print all parse items as they are inferred. Plus statistics
           about the grammar and the final chart.
    """

    def __init__(self, mcfrules, startcats,
                 probabilities=None, weights=None,
                 check=True, trace=None, 
                 nonempty=False, topdown=False, bottomup=False, filtered=False):
        """
        Create a PMCFG parser. 

        Keyword arguments:
        mcfrules  -- a sequence or an iterator of (fun, cat, args, rhss) tuples.
                     'fun' is the name of the rule, 'cat' is the lefthandside
                     nonterminal, and 'args' is a tuple/list of nonterminals.
                     'rhss' is a dict/list of linearization sequences.
        startcats -- a list/tuple/set of starting nonterminals.
        probabilities, weights -- mutually exclusive
        check     -- perform sanity check on the grammar rules.
        trace     -- the general tracing level for all methods (None/0/1/2).
        nonempty  -- transform the grammar to non-empty form (this can in some
                     cases improve performance, especially for bottomup parsing).
        topdown   -- perform topdown parsing (this is the default strategy).
        bottomup  -- perform bottomup parsing. 
        filtered  -- perform left-corner filtering (works with topdown/bottomup).
        """

        if isinstance(mcfrules, dict):
            mcfrules = mcfrules.iteritems()
        if check:
            if not isinstance(mcfrules, (list, tuple, set)):
                mcfrules = list(mcfrules)
            check_grammar_rules(mcfrules)

        if not (topdown or bottomup):
            topdown = True
        elif topdown and bottomup:
            raise ValueError("The parsing strategy cannot be both bottomup and topdown.")
        self.strategy = {'topdown':topdown, 'bottomup':bottomup, 'filtered':filtered}

        self.nonempty = nonempty
        self.trace = trace
        self.chart = {}
        self.statistics = {}
        self.grammar = {}
        if isinstance(startcats, basestring):
            startcats = [startcats]
        if not isinstance(startcats, (list, tuple, set)):
            raise TypeError("Unexpected type for starting categories: %s" % type(startcats).__name__)
        self.grammar['startcats'] = startcats

        if probabilities:
            if weights:
                raise ValueError("Either probabilities or weights, not both!")
            assert all(0 <= p <= 1 for p in probabilities.itervalues())
            weights = dict((key, -math.log(prob)) for (key, prob) in probabilities.iteritems())
        if weights:
            assert all(0 <= w for w in weights.itervalues())
            self.grammar['weights'] = weights

        initialize_topdown_grammar(self.grammar, mcfrules, self.trace)
        if self.grammar['is_empty'] and self.nonempty: 
            remove_emptyrules(self.grammar, self.trace)
        if self.strategy['filtered']:
            initialize_emptycats(self.grammar, self.trace)
            initialize_leftcorners(self.grammar, self.trace)
            # if self.grammar['is_empty']:
            #     self._init_emptyfollowers()
        # TODO: empty followers does not work (yet)
        # if self.bottomup and not self.filtered:
        #     self._init_emptycats()
        #     self._init_leftcorner()
        #     self._init_emptyfollowers()
        if self.strategy['bottomup']:
            initialize_bottomup_grammar(self.grammar, self.trace)
        if self.trace > 1: 
            self.print_grammar_statistics()

    ######################################################################
    ## Parsing

    def parse(self, tokens, n=None, trace=None):
        """
        Parse a sequence of tokens, returns an iterator of parse trees.

        Keyword arguments:
        tokens -- a list/tuple of tokens (e.g., strings).
        n      -- the maximum number of parse trees to be returned.
        trace  -- the tracing level (None/0/1/2).
        """
        self.chart_parse(tokens, trace)
        return self.extract_trees(n=n)

    def chart_parse(self, tokens, trace=None):
        """
        Parse a sequence of tokens, returns True if parsing succeeds.

        If parsing succeeds, you can use the method .extract_trees()
        to get the parse trees.

        Keyword arguments:
        tokens -- a list/tuple of tokens (e.g., strings).
        n      -- the maximum number of parse trees to be returned.
        trace  -- the tracing level (None/0/1/2).
        """
        if trace is None: trace = self.trace
        self.init_chart(tokens)
        if trace == 1: 
            ctr = TracedCounter("Parse: ", interval=1) # TODO: print strategy
        for k in self.positions:
            if k > 0 and trace == 1: ctr.inc(tokens[k-1][0])
            self.process_token(k, trace)
        stat = self.statistics['Chart']
        if not stat:
            for key, chrt in self.chart.iteritems():
                key = getattr(key, '__name__', key)
                stat[key] = objsize(chrt)
        for stat in self.statistics.itervalues():
            if isinstance(stat, dict):
                stat['TOTAL'] = sum(stat[key] for key in stat if key != 'TOTAL'
                                    if isinstance(stat[key], (int, long, float)))
        if trace == 1: 
            ctr.finalize()
        elif trace > 1:
            self.print_parse_statistics()
        return any(Found(startcat, lbl, 0, len(tokens)) in self.chart[Rule]
                   for startcat in self.grammar['startcats']
                   for lbl in self.grammar['catlabels'][startcat])

    def extract_trees(self, startcats=None, start=0, end=None, n=None):
        """
        Returns a generator that extracts all parse trees from the chart.

        Keyword arguments:
        startcats -- The toplevel nonterminal(s) to use.
                     (Default: taken from the grammar).
        start, end -- The start resp. end positions to extract from.
                      (Default: spanning the whole sentence).
        n      -- the maximum number of parse trees to be returned.
        """
        if end is None:
            end = len(self.tokens)
        if startcats is None:
            startcats = self.grammar['startcats']
        emptyrules = self.grammar.get('emptyrules', {})
        ctr = 0
        for cat in startcats:
            for lbl in self.grammar['catlabels'][cat]:
                topcat = Found(cat, lbl, start, end)
                for tree in generate_trees(topcat, self.chart[Rule], backup_rules=emptyrules, visited=set()):
                    yield tree
                    ctr += 1
                    if n and ctr >= n: 
                        return

    def process_token(self, k, trace=None):
        """Process the token at position k, adding to the internal chart."""
        if trace is None: trace = self.trace
        process_token(k, self.tokens, self.chart, self.statistics, self.grammar, trace=trace, **self.strategy)

    def init_chart(self, tokens):
        """Initialize the chart before parsing."""
        if not isinstance(tokens, (list, tuple)):
            raise TypeError("Tokens must be a list or a tuple of strings")
        self.tokens = tokens
        self.positions = range(1 + len(tokens))
        self.chart = {}
        self.chart[Active] = [defaultdict(set) for _ in self.positions]
        self.chart[Found] = [[set() for _ in self.positions] for _ in self.positions]
        self.chart[Rule] = defaultdict(set)
        if self.grammar['is_empty']:
            self.chart[Symbol] = [defaultdict(set) for _ in self.positions]
        else:
            self.chart[Symbol] = [set() for _ in self.positions]
        self.statistics = {}
        self.statistics['Time'] = 0.0
        self.statistics['Chart'] = defaultdict(int) 
        self.statistics['Inferences'] = defaultdict(int)

    ######################################################################
    ## Pretty-printing

    def print_chart(self):
        """Print the chart in MultiMarkdown format."""
        print_chart(self.chart, self.tokens, self.grammar['startcats'], self.grammar['sequences'])

    def print_parse_statistics(self):
        """Print a MultiMarkdown table with statistics from parsing."""
        statkeys = [set(stat) for stat in self.statistics.itervalues() if isinstance(stat, dict)]
        total_first = lambda key: None if key == "TOTAL" else key
        statkeys = sorted(set.union(*statkeys), key=total_first)
        print "Statistics |" + "".join("%9s |" % (key,) for key in statkeys)
        print "-----------|" + "".join("---------:|" for key in statkeys)
        for hdr, stat in self.statistics.iteritems():
            if isinstance(stat, dict):
                print "%-11s|" % (hdr,) + "".join("%9s |" % (stat.get(key, "--"),) for key in statkeys)
        for hdr, value in self.statistics.iteritems():
            if not isinstance(value, dict):
                if isinstance(value, float):
                    value = "%8.2f"  % (value,)
                print "%-11s|%9s |" % (hdr, value)

    def print_grammar_statistics(self):
        """Print a MultiMarkdown table with statistics of the grammar."""
        print "Grammar statistics          ||"
        print "-------------------|--------:|"
        print "Nr. terminals      |%8d |" % len(set(word for rhss in self.grammar['sequences'].itervalues()
                                                    for rhs in rhss.itervalues() for word in rhs 
                                                    if type(word) is not RHSSymbol))
        print "Nr. nonterminals   |%8d |" % len(set(self.grammar['catlabels']))
        print "Nr. nonterm-const. |%8d |" % objsize(self.grammar['catlabels'])
        print "Nr. grammar rules  |%8d |" % objsize(self.grammar['topdown'])
        print "Epsilon-free       |%8s |" % (not self.grammar['is_empty'],)
        if 'emptyrules' in self.grammar:
            print "Nr. empty rules    |%8d |" % objsize(self.grammar['emptyrules'])
        print "Nr. constituents   |%8d |" % sum(len(self.grammar['sequences'][rule.fun]) 
                                                   for rules in self.grammar['topdown'].itervalues() 
                                                   for rule in rules)
        print "Nr. const. lengths |%8d |" % sum(len(rhs) 
                                                   for rules in self.grammar['topdown'].itervalues() 
                                                   for rule in rules
                                                   for rhs in self.grammar['sequences'][rule.fun].itervalues())
        if 'emptycats' in self.grammar:
            print "Nr. empty const.   |%8d |" % len(self.grammar['emptycats'])
        if 'leftcorner' in self.grammar:
            print "Nr. leftc. pairs   |%8d |" % objsize(self.grammar['leftcorner'])
            print "Nr. lcword. pairs  |%8d |" % objsize(self.grammar['lcwords'])


######################################################################
## Grammar sanity check

def check_grammar_rules(mcfrules):
    """Check that the grammar rules are in correct format."""
    catlabels = {}
    sequences = {}
    for nr, mcfrule in enumerate(mcfrules):
        try:
            fun, cat, args, rhss = split_mcfrule(mcfrule)
        except:
            raise TypeError("MCF rule %d: Rule must be a tuple of the form (fun, cat, args, rhss) "
                            "or ((fun, cat, args), rhss)" % (nr,))
        preerror = "MCF rule %d, %r: " % (nr, fun)

        if not isinstance(args, (list, tuple)):
            raise TypeError(preerror + "Rule arguments must be a list or a tuple of categories, "
                            "not %r" % (type(args).__name,))
        if any(isinstance(c, (list, set, dict)) for c in [cat] + list(args)):
            raise TypeError(preerror + "Grammar category must not be a mutable object")

        if isinstance(rhss, (list, tuple)):
            rhss = dict(enumerate(rhss))
        elif not isinstance(rhss, dict):
            raise TypeError(preerror + "Right-hand side must be a list, tuple or dict, "
                            "not %r" % (type(rhss).__name__,))

        lbls = sorted(rhss.iterkeys())
        if cat not in catlabels:
            catlabels[cat] = lbls
        elif catlabels[cat] != lbls:
            raise ValueError(preerror + "Inconsistent right-hand side labels: "
                             "%s != %s" % (lbls, catlabels[cat]))

        lbltypes = set(map(type, rhss.iterkeys()))
        if len(lbltypes) > 1:
            raise TypeError(preerror + "Inconsistent label types in right-hand side: %s" %
                            (", ".join(map(repr, lbltypes)),))

        if lbltypes:
            lbltype = lbltypes.pop()
            for lbl, rhs in rhss.iteritems():
                if not isinstance(rhs, (list, tuple)):
                    raise TypeError(preerror + "Right-hand side sequence must be a list or a tuple, "
                                    "not %r" % (type(rhs).__name__,))
                for sym in rhs:
                    if isinstance(sym, tuple):
                        if not (len(sym) == 2 and isinstance(sym[0], int) and type(sym[1]) is lbltype):
                            raise TypeError(preerror + "Argument references in right-hand sides must "
                                            "be (%r,%r) tuples" % (int.__name__, lbltype.__name__))
                    elif isinstance(sym, (list, dict, set)):
                        raise TypeError(preerror + "Right-hand side symbols must be simple types, "
                                        "not %r" % (type(sym).__name__,))

        if fun not in sequences:
            sequences[fun] = rhss
        elif sequences[fun] != rhss:
            raise ValueError(preerror + "Inconsistent right-hand-sides")


def split_mcfrule(mcfrule):
    try: 
        (fun, cat, args), rhss = mcfrule
    except ValueError:
        try: 
            fun, (cat, args, rhss) = mcfrule
        except ValueError:
            fun, cat, args, rhss = mcfrule
    return fun, cat, args, rhss


######################################################################
## Initializing and optimizing the grammar

def initialize_topdown_grammar(grammar, mcfrules, trace=None):
    """
    Convert the mcfrules to a grammar suitable for topdown parsing.
    The topdown grammar is stored in grammar['topdown'], and the
    linearization sequences are stored in grammar['sequences'].
    """
    if trace: ctr = TracedCounter("Topdown grammar:")
    td_grammar = grammar['topdown'] = defaultdict(list)
    catlabels = grammar['catlabels'] = {}
    sequences = grammar['sequences'] = {}

    for mcfrule in mcfrules:
        fun, cat, args, rhss = split_mcfrule(mcfrule)

        convertsym = lambda sym: (RHSSymbol(*sym) 
                                  if isinstance(sym, tuple) and type(sym) is not RHSSymbol 
                                  else sym)

        rhssitems = (enumerate(rhss) 
                     if isinstance(rhss, (list, tuple))
                     else rhss.iteritems())
        rhss = dict((lbl, map(convertsym, rhs)) for (lbl, rhs) in rhssitems)

        lbls = sorted(rhss.iterkeys())
        catlabels[cat] = lbls
        sequences[fun] = rhss

        rule = Rule(fun, cat, tuple(args))
        td_grammar[cat].append(rule)
        if trace: ctr.inc()

    grammar['is_empty'] = not all(rhs for rhss in sequences.itervalues() for rhs in rhss.itervalues())
    if trace: ctr.finalize()


def initialize_bottomup_grammar(grammar, trace=None):
    """
    Convert the grammar to a format suitable for bottomup parsing.
    The bottomup grammar is stored in grammar['bottomup'], and it requires 
    that grammar['topdown'] and grammar['sequences'] are already calculated.
    """
    td_grammar = grammar['topdown']
    sequences = grammar['sequences']
    bu_grammar = grammar['bottomup'] = defaultdict(list)
    if trace: ctr = TracedCounter("Bottomup grammar:")
    for tdrules in td_grammar.itervalues():
        for rule in tdrules:
            rhss = sequences[rule.fun]
            for lbl, rhs in rhss.iteritems():
                if not rhs:
                    first = None
                else:
                    first = rhs[0]
                    if type(first) is RHSSymbol:
                        first = first.toSymbol(rule.args)
                bu_grammar[first].append(BottomupRule(rule, lbl, Symbol(rule.cat, lbl)))
                if trace: ctr.inc()
    if trace: ctr.finalize()


def initialize_emptycats(grammar, trace=None):
    """
    Calculates the constituents that can recognize the empty string.
    The empty constituents are stored as a set in grammar['emptycats'], 
    and it requires that grammar['topdown'] and grammar['sequences'] 
    are already calculated.
    """
    td_grammar = grammar['topdown']
    sequences = grammar['sequences']
    emptycats = grammar['emptycats'] = set()
    if not grammar['is_empty']:
        return
    if trace: ctr = TracedCounter("Empty categories:")
    agenda = [(0, rule, lbl) 
              for tdrules in td_grammar.itervalues()
              for rule in tdrules
              for lbl, rhs in sequences[rule.fun].iteritems()
              if not rhs or type(rhs[0]) is RHSSymbol]
    empty_predicts = defaultdict(set)
    while agenda:
        pos, rule, lbl = agenda.pop()
        rhs = sequences[rule.fun][lbl]
        if pos >= len(rhs): 
            sym = Symbol(rule.cat, lbl)
            if sym not in emptycats:
                emptycats.add(sym)
                agenda.extend(empty_predicts[sym])
                if trace: ctr.inc()
        elif type(rhs[pos]) is RHSSymbol:
            argsym = rhs[pos].toSymbol(rule.args)
            if argsym in emptycats:
                agenda.append((pos + 1, rule, lbl))
            else:
                empty_predicts[argsym].add((pos + 1, rule, lbl))
    if trace: ctr.finalize()
    assert all(type(sym) is Symbol for sym in emptycats)


def initialize_leftcorners(grammar, trace=None):
    """
    Calculate the left-corner tables from the grammar.
    The tables are stored in grammar['leftcorner'] and grammar['lcword'].
    It requires that grammar['topdown'], grammar['sequences'] and 
    grammar['emptycats'] are already calculated.
    """
    td_grammar = grammar['topdown']
    sequences = grammar['sequences']
    emptycats = grammar['emptycats'] 
    leftcorner_words = grammar['lcwords'] = defaultdict(set)
    leftcorner = grammar['leftcorner'] = defaultdict(set)

    if trace: ctr = TracedCounter("Leftcorners:")
    leftcorner_parents = defaultdict(set)
    for tdrules in td_grammar.itervalues():
        for rule in tdrules:
            rhss = sequences[rule.fun]
            for lbl, rhs in rhss.iteritems():
                parent = Symbol(rule.cat, lbl)
                for sym in rhs:
                    if trace: ctr.inc()
                    if type(sym) is not RHSSymbol:
                        leftcorner_words[sym].add(parent)
                        break
                    sym = sym.toSymbol(rule.args)
                    leftcorner_parents[sym].add(parent)
                    if sym not in emptycats:
                        break

    for sym, parents in leftcorner_parents.iteritems():
        agenda = list(parents)
        while agenda:
            parent = agenda.pop()
            if parent not in leftcorner[sym]:
                leftcorner[sym].add(parent)
                if trace: ctr.inc()
                if leftcorner[parent]:
                    leftcorner[sym].update(leftcorner[parent])
                elif parent in leftcorner_parents:
                    agenda.extend(leftcorner_parents[parent])

    for (cat, lbls) in grammar['catlabels'].iteritems():
        for lbl in lbls:
            sym = Symbol(cat, lbl)
            leftcorner[sym].add(sym)
            if trace: ctr.inc()
    if trace: ctr.finalize()

    assert all(type(first) is Symbol and type(parent) is Symbol 
               for first, parents in grammar['leftcorner'].iteritems() 
               for parent in parents)
    assert all(not isinstance(word, (tuple, list, set, dict)) and type(parent) is Symbol
               for word, parents in grammar['lcwords'].iteritems()
               for parent in parents)


def initialize_emptyfollowers(grammar, trace=None):
    """
    Calculate what tokens can follow after each constituent.
    The followers are stored in grammar['emptyfollowers'].
    It requires that grammar['topdown'], grammar['sequences'],
    grammar['emptycats'] and grammar['leftcorner'] are calculated.

    NOTE: This is not working properly yet!
    """
    emptyfollowers = grammar['emptyfollowers'] = defaultdict(set)
    if trace: ctr = TracedCounter("Empty followers:")
    td_grammar = grammar['topdown']
    sequences = grammar['sequences']
    emptycats = grammar['emptycats'] 
    leftcorner = grammar['leftcorner']
    direct_predecessors = defaultdict(set)

    for tdrules in td_grammar.itervalues():
        for rule in tdrules:
            rhss = sequences[rule.fun]
            for lbl, rhs in rhss.iteritems():
                for (before, after) in zip(rhs, rhs[1:]):
                    if type(before) is RHSSymbol:
                        before = before.toSymbol(rule.args)
                        if before in emptycats:
                            if type(after) is RHSSymbol:
                                after = after.toSymbol(rule.args)
                            #     direct_predecessors[after].add(before)
                            # else:
                            #     emptyfollowers[before].add(after)
                            emptyfollowers[before].add(after)
                            if trace: ctr.inc()

    # for after, parents in leftcorner.iteritems():
    #     for parent in parents:
    #         for before in direct_predecessors[parent]:
    #             emptyfollowers[before].add(after)
    #             if trace: ctr.inc()
    # if trace: ctr.finalize()

    assert all(type(before) is Symbol and before in emptycats 
               for before, afters in emptyfollowers.iteritems() for after in afters)


######################################################################
## Transforming the grammar

# NOTE: None of these two are correct, there are grammars for which 
# the transformation is not equivalent.

def remove_emptyrules(grammar, trace=None):
    """
    Remove rules with empty constituents from the grammar.
    Requires that grammar['topdown'] and grammar['sequences']
    are calculated. The old topdown grammar and sequences
    are replaced by the new nonempty grammar, as are
    grammar['catlabels'], grammar['is_empty']. 
    The removed rules are put in grammar['emptyrules'].

    NOTE: This transformation does not always produce an 
    equivalent grammar!
    """
    if trace: ctr = TracedCounter("Remove emptyrules:", interval=1000)
    sequences = grammar['sequences']
    cats = set()
    agenda = set()
    newrules = set()
    emptyrules = set()
    argrules = defaultdict(lambda:defaultdict(set))

    for cat, rules in grammar['topdown'].iteritems():
        cats.add(cat)
        newrules.update(rules)
        for rule in rules:
            rhss = sequences[rule.fun]
            if not all(rhss.itervalues()):
                agenda.add(rule)
            for argnr, arg in enumerate(rule.args):
                argrules[arg][rule].add(argnr)

    while agenda:
        rule = agenda.pop()
        rhss = sequences[rule.fun]
        assert rule.fun not in emptyrules, rule
        emptyrules.add(rule)

        elbls = set(lbl for lbl, rhs in rhss.iteritems() if not rhs)
        elblstr = repr(sorted(elbls))
        newfun = NEFun(rule.fun, elblstr)
        assert type(rule.fun) is not NEFun, newfun
        newcat = NECat(rule.cat, elblstr)
        assert type(rule.cat) is not NECat, newfun
        newrule = Rule(newfun, newcat, rule.args)
        assert newrule not in newrules, newrule
        newrules.add(newrule)
        if trace: ctr.inc()

        newrhss = dict((lbl, rhs) for (lbl, rhs) in rhss.iteritems() if rhs)
        if newfun in sequences:
            assert sequences[newfun] == newrhss
        else:
            sequences[newfun] = newrhss
        if not newrhss:
            emptyrules.add(newrule)

        if newcat not in cats:
            cats.add(newcat)
            for xrule, xnrs in argrules[rule.cat].items():
                # This is really necessary for correctness, but it takes LOOOONG time:
                # for xnrs in powerset(xnrs):
                    if xnrs:
                        newxcat = xrule.cat
                        newxargs = tuple(newcat if xnr in xnrs else xarg 
                                         for (xnr, xarg) in enumerate(xrule.args))
                        assert type(xrule.fun) is not NEFun, xrule
                        newxfun = SFun(get_orig(xrule.fun), newxargs)
                        newxrule = Rule(newxfun, newxcat, newxargs)
                        assert newxrule not in newrules, newxrule
                        newrules.add(newxrule)
                        for xnr, xarg in enumerate(newxargs):
                            argrules[xarg][newxrule].add(xnr)
                        if trace: ctr.inc()

                        newxrhss = dict((lbl, [sym for sym in rhs 
                                               if not (type(sym) is RHSSymbol and 
                                                       sym.arg in xnrs and sym.lbl in elbls)])
                                        for (lbl, rhs) in sequences[xrule.fun].iteritems())
                        assert newxfun not in sequences, newxrule
                        sequences[newxfun] = newxrhss
                        if not all(newxrhss.itervalues()):
                            agenda.add(newxrule)

    grammar['emptyrules'] = defaultdict(set)
    for erule in emptyrules:
        newrules.remove(erule)
        if erule.fun in sequences:
            del sequences[erule.fun]
        newrule = Rule(get_orig(erule.fun), get_orig(erule.cat), tuple(map(get_orig, erule.args)))
        grammar['emptyrules'][newrule.cat].add(newrule)

    grammar['topdown'].clear()
    grammar['catlabels'] = {}
    for rule in newrules:
        cat = rule.cat
        grammar['topdown'][cat].append(rule)
        if get_orig(cat) in grammar['startcats'] and cat not in grammar['startcats']:
            grammar['startcats'].append(cat)
        rulelbls = sorted(sequences[rule.fun])
        if cat in grammar['catlabels']:
            assert grammar['catlabels'][cat] == rulelbls
        else:
            grammar['catlabels'][cat] = rulelbls

    grammar['is_empty'] = not all(rhs for rhss in sequences.itervalues() for rhs in rhss.itervalues())
    if trace: ctr.finalize()

    assert not grammar['is_empty']
    assert all(not isinstance(cat, (list, set, dict)) and type(rule) is Rule 
               for cat, rules in grammar['topdown'].iteritems() 
               for rule in rules)


def remove_emptyrules_alternative(grammar, trace=None):
    """
    Remove rules with empty constituents from the grammar.
    Requires that grammar['topdown'] and grammar['sequences']
    are calculated. The old topdown grammar and sequences
    are replaced by the new nonempty grammar, as are
    grammar['catlabels'], grammar['is_empty']. 
    The removed rules are put in grammar['emptyrules'].

    NOTE: This is an alternative algorithm, which unfortunately
    does not either produce an equivalent grammar...
    """
    if trace: ctr = TracedCounter("Remove emptyrules:", interval=1000)
    oldrules = grammar['topdown']
    sequences = grammar['sequences']
    newcats = set()
    agenda = set()
    argrules = defaultdict(lambda:defaultdict(set))
    newrules = set()
    newseqs = {}
    startcats = grammar['startcats']
    newstarts = set()

    for cat in oldrules:
        for rule in oldrules[cat]:
            if rule.args:
                for nr, arg in enumerate(rule.args):
                    argrules[arg][rule].add(nr)
            else:
                rhss = sequences[rule.fun]
                newrhss = dict((lbl, rhs) for (lbl, rhs) in rhss.iteritems() if rhs)
                lbls = tuple(sorted(newrhss))
                newcat = NECat(rule.cat, lbls)
                newfun = NEFun(rule.fun, (newcat,))
                newrule = Rule(newfun, newcat, ())
                newrules.add(newrule)
                if newfun in newseqs:
                    assert newseqs[newfun] == newrhss
                else:
                    newseqs[newfun] = newrhss
                agenda.add(newcat)

    while agenda:
        newarg = agenda.pop()
        if newarg in newcats: 
            continue
        newcats.add(newarg)
        for rule, argnrs in argrules[newarg.orig].items():
            # This is really necessary for correctness, but it takes LOOOONG time:
            # for argnrs in powerset(argnrs): 
                if argnrs: 
                    newargs = tuple(newarg if nr in argnrs else arg 
                                    for (nr, arg) in enumerate(rule.args))
                    if any(type(arg) is not NECat for arg in newargs):
                        newrule = Rule(rule.fun, rule.cat, newargs)
                        for nr, arg in enumerate(newargs):
                            if type(arg) is not NECat:
                                argrules[arg][newrule].add(nr)
                    else:
                        rhss = sequences[rule.fun]
                        newrhss = {}
                        for lbl, rhs in sequences[rule.fun].iteritems():
                            newrhs = [sym for sym in rhs if (type(sym) is not RHSSymbol or
                                                             sym.lbl in newargs[sym.arg].lbls)]
                            if newrhs:
                                newrhss[lbl] = newrhs
                        lbls = tuple(sorted(newrhss))
                        newcat = NECat(rule.cat, lbls)
                        newfun = NEFun(rule.fun, (newcat,) + newargs)
                        newrule = Rule(newfun, newcat, newargs)
                        newrules.add(newrule)
                        if newfun in newseqs:
                            assert newseqs[newfun] == newrhss
                        else:
                            newseqs[newfun] = newrhss
                        if newcat not in newcats:
                            agenda.add(newcat)
                    if trace: ctr.inc()

    catlabels = {}
    emptyrules = defaultdict(set)
    oldrules.clear()
    sequences.clear()
    for rule in newrules:
        rulecatlbls = rule.cat.lbls
        rhss = newseqs[rule.fun]
        if rhss and all(rhss.itervalues()):
            fun = NEFun(rule.fun, "+".join(map(str, rule.fun.lbls)))
            cat = NECat(rule.cat, str(rule.cat.lbls))
            args = tuple(NECat(arg, str(arg.lbls)) for arg in rule.args)
            rule = Rule(fun, cat, args)
            oldrules[rule.cat].append(rule)
            sequences[rule.fun] = rhss
        else:
            rule = Rule(get_orig(rule.fun), get_orig(rule.cat), tuple(map(get_orig, rule.args)))
            emptyrules[rule.cat].add(rule)
        if rule.cat in catlabels:
            assert catlabels[rule.cat] == rulecatlbls
        else:
            catlabels[rule.cat] = rulecatlbls
        if get_orig(rule.cat) in startcats:
            newstarts.add(rule.cat)

    grammar['startcats'] = newstarts
    grammar['catlabels'] = catlabels
    grammar['emptyrules'] = emptyrules
    grammar['is_empty'] = not all(rhs for rhss in sequences.itervalues() for rhs in rhss.itervalues())

    if trace: ctr.finalize()

    assert not grammar['is_empty']
    assert all(not isinstance(cat, (list, set, dict)) and type(rule) is Rule 
               for cat, rules in grammar['topdown'].iteritems() 
               for rule in rules)


# remove_emptyrules = remove_emptyrules_alternative


######################################################################
## Generating syntax trees from a set of grammar rules

def generate_trees(cat, rules, backup_rules={}, visited=set()):
    """
    Generate all syntax trees from a set of rules.
    The backup_rules are used if the category is not found in 
    the given rules.
    """
    catrules = rules.get(cat)
    if not catrules: 
        cat = get_orig(cat)
        catrules = backup_rules.get(cat, ())
        rules, backup_rules = backup_rules, {}
    for rule in catrules:
        if rule not in visited:
            visited_copy = visited | set([rule])
            assert rule.cat == cat, (cat, rule)
            fun = get_orig(rule.fun)
            for children in generate_children(0, rule.args, rules, backup_rules, visited_copy):
                yield (fun,) + children

def generate_children(nr, args, rules, backup_rules, visited):
    """
    Generate all children sequences from args, a sequence of nonterminals.
    """
    if nr >= len(args): 
        yield ()
    else:
        for child in generate_trees(args[nr], rules, backup_rules, visited):
            for children in generate_children(nr+1, args, rules, backup_rules, visited):
                yield (child,) + children


######################################################################
## Parsing one token at the time

def process_token(k, tokens, chart, statistics, grammar, trace=None, **strategy):
    """Process token nr k, adding items to the chart."""
    if trace > 1:
        token = '"%s"' % (tokens[k-1],) if k > 0 else "---"
        header = "State %d: %s" % (k, token)
        print "%-30s|||" % (header,)
        print "--------|---------------------|-------------------------"

    agenda = []
    if not trace:
        def add_edge(edge, edgeset, name, *antecedents):
            if edge not in edgeset:
                edgeset.add(edge)
                agenda.append(edge)
    else:
        chart['edgecounter'] = 0
        chart.setdefault('edgeids', {})
        def add_edge(edge, edgeset, name, *antecedents):
            statistics['Inferences'][type(edge).__name__] += 1
            if edge not in edgeset:
                edgeset.add(edge)
                agenda.append(edge)
                statistics['Chart'][type(edge).__name__] += 1
                if trace > 1: 
                    chart['edgecounter'] += 1
                    edgeid = "%d:%d" % (k, chart['edgecounter'])
                    chart['edgeids'][edge] = edgeid
                    antecedents = [chart['edgeids'][ant] for ant in antecedents]
                    trace_edge(name, edge, k, edgeid, grammar['sequences'], antecedents)

    starttime = time.clock()
    if grammar['is_empty']:
        process_token_emptygrammar(k, tokens, chart, grammar, agenda, add_edge, **strategy)
    else:
        process_token_nonempty(k, tokens, chart, grammar, agenda, add_edge, **strategy)
    statistics['Time'] += time.clock() - starttime

    if trace > 1:
        if not chart['edgecounter']:
            print "                              |||"
        print


######################################################################
## parsing grammars with epsilon rules

def process_token_emptygrammar(k, tokens, chart, grammar, agenda, add_edge, topdown, bottomup, filtered):
    """Process token nr k, if the grammar contains empty constituents."""
    assert bool(topdown) != bool(bottomup), "Parsing should be either topdown or bottomup"
    sequences = grammar['sequences']
    active_chart = chart[Active]
    predict_chart = chart[Symbol]
    found_chart = chart[Found]
    dynrule_chart = chart[Rule]

    if k == 0:
        if topdown or filtered:
            # initial topdown predict
            for startcat in grammar['startcats']:
                for lbl in grammar['catlabels'][startcat]:
                    predict = Symbol(startcat, lbl)
                    add_edge(predict, predict_chart[k][startcat], "init TD")

    else:
        # scan
        for active in active_chart[k-1][tokens[k-1]]:
            assert k-1 == active.end, (k-1, active.end, active)
            add_active_edge(active.start, k, active.lbl, active.pos+1, active.rule, sequences, active_chart, add_edge, "scan", active)

        if bottomup:
            # scan bottomup 
            if not filtered:
                for burule in grammar['bottomup'][tokens[k-1]]:
                    add_active_edge(k-1, k, burule.lbl, 1, burule.rule, sequences, active_chart, add_edge, "scan BU")
            else:
                predicts = predict_chart[k-1]
                if predicts:
                    for burule in grammar['bottomup'][tokens[k-1]]:
                        if not predicts.isdisjoint(grammar['leftcorner'][burule.sym]):
                            add_active_edge(k-1, k, burule.lbl, 1, burule.rule, sequences, active_chart, add_edge, "scan BU")

    if bottomup and not filtered:
        # scan epsilon
        for burule in grammar['bottomup'][None]:
            # TODO: DOESN'T WORK:
            # sym = Symbol(rule.cat, lbl)
            # assert sym in grammar['emptycats']
            # if k < len(tokens):
            #     followers = grammar['emptyfollowers'][sym]
            #     print show_sym(sym), ":", " ".join(map(show_sym, followers))
            #     next_token = tokens[k]
            #     print next_token, "/", " ".join([show_sym(parent) for child in grammar['lcwords'][next_token] for parent in grammar['leftcorner'][child]])
            #     if not (next_token in followers or
            #             any(parent in followers
            #                 for child in grammar['lcwords'][next_token]
            #                 for parent in grammar['leftcorner'][child])):
            #         continue
            #     # if next_token not in followers and followers.isdisjoint(grammar['lcwords'][next_token]):
            #     #     continue
            add_active_edge(k, k, burule.lbl, 0, burule.rule, sequences, active_chart, add_edge, "scan empty")

    # process agenda
    while agenda:
        edge = agenda.pop()
        if type(edge) is Active:
            active = edge
            nextsym = active.nextsym
            rule = active.rule
            assert k == active.end, (k, active.end, active)
            if nextsym is None:
                # complete
                found = Found(rule.cat, active.lbl, active.start, k)
                newrule = Rule(rule.fun, found, rule.args)
                add_edge(found, found_chart[k][active.start], "complete", active)
                add_edge(newrule, dynrule_chart[found], "complete", active)

            elif type(nextsym) is Symbol:
                # predict item
                add_edge(nextsym, predict_chart[k][nextsym.cat], "pred. item", active)
                # combine
                found = Found(nextsym.cat, nextsym.lbl, k, k)
                if found in found_chart[k][k]:
                    combine_inference_rule(active, found, sequences, active_chart, add_edge, "combine", active, found)

        elif type(edge) is Rule:
            # predict next
            rule = edge
            cat = rule.cat
            assert k == cat.end, (k, cat.end, rule)
            for predict in predict_chart[k][cat]:
                assert cat == predict.cat, (cat, predict.cat)
                add_active_edge(k, k, predict.lbl, 0, rule, sequences, active_chart, add_edge, "pred. next", rule, predict)

        elif type(edge) is Symbol:
            predict = edge
            cat = predict.cat
            if type(cat) is Found:
                # predict next
                for rule in dynrule_chart[cat]:
                    assert cat == rule.cat, (cat, rule.cat)
                    add_active_edge(k, k, predict.lbl, 0, rule, sequences, active_chart, add_edge, "pred. next", rule, predict)

            elif topdown:
                if (not filtered
                    or predict in grammar['emptycats']
                    or k < len(tokens) and leftcorner_predict_token(predict, tokens[k], grammar)
                ):
                    # predict topdown
                    for rule in grammar['topdown'][predict.cat]:
                        add_active_edge(k, k, predict.lbl, 0, rule, sequences, active_chart, add_edge, "pred. TD", predict)

            elif bottomup and filtered:
                # scan epsilon
                for burule in grammar['bottomup'][None]:
                    if predict in grammar['leftcorner'][burule.sym]:
                        add_active_edge(k, k, burule.lbl, 0, burule.rule, sequences, active_chart, add_edge, "scan empty", predict)

                # predict bottomup
                for found in found_chart[k][k]:
                    assert k == found.start == found.end, (k, found.start, found.end, found)
                    nextsym = Symbol(found.cat, found.lbl)
                    for burule in grammar['bottomup'][nextsym]:
                        if predict in grammar['leftcorner'][burule.sym]:
                            active = Active(k, k, burule.lbl, nextsym, 0, burule.rule)
                            combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred. BU", predict, found)

        elif type(edge) is Found:
            found = edge
            assert k == found.end, (k, found.end, found)
            start = found.start
            nextsym = Symbol(found.cat, found.lbl)
            # combine
            for active in active_chart[start][nextsym]:
                combine_inference_rule(active, found, sequences, active_chart, add_edge, "combine", active, found)

            if bottomup:
                # predict bottomup
                if not filtered:
                    for burule in grammar['bottomup'][nextsym]:
                        active = Active(start, start, burule.lbl, nextsym, 0, burule.rule)
                        combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred. BU", found)
                else:
                    predicts = predict_chart[start]
                    if predicts:
                        if start == k:
                            predicts = set.union(*predicts.itervalues())
                        for burule in grammar['bottomup'][nextsym]:
                            if not predicts.isdisjoint(grammar['leftcorner'][burule.sym]):
                                active = Active(start, start, burule.lbl, nextsym, 0, burule.rule)
                                combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred. BU", found)

        else:
            assert False, (type(edge), edge)

    predict_chart[k] = set().union(*predict_chart[k].itervalues())




######################################################################
## parsing grammars with no epsilon rules

def process_token_nonempty(k, tokens, chart, grammar, agenda, add_edge, topdown, bottomup, filtered):
    """Process token nr k, if the grammar does not contain empty constituents."""
    assert bool(topdown) != bool(bottomup), "Parsing should be either topdown or bottomup"
    sequences = grammar['sequences']
    active_chart = chart[Active]
    predict_chart = chart[Symbol]
    found_chart = chart[Found]
    dynrule_chart = chart[Rule]

    # scan, scan-BU
    if k > 0:
        # scan
        for active in active_chart[k-1][tokens[k-1]]:
            assert k-1 == active.end, (k-1, active.end, active)
            add_active_edge(active.start, k, active.lbl, active.pos+1, active.rule,
                            sequences, active_chart, add_edge, "scan", active)

        if bottomup:
            # scan bottomup 
            if not filtered:
                for burule in grammar['bottomup'][tokens[k-1]]:
                    add_active_edge(k-1, k, burule.lbl, 1, burule.rule, sequences, active_chart, add_edge, "scan BU")
            else:
                predicts = predict_chart[k-1]
                if predicts:
                    for burule in grammar['bottomup'][tokens[k-1]]:
                        if not predicts.isdisjoint(grammar['leftcorner'][burule.sym]):
                            add_active_edge(k-1, k, burule.lbl, 1, burule.rule, sequences, active_chart, add_edge, "scan BU")

    # complete, combine, predict-BU
    while agenda:
        edge = agenda.pop()

        if type(edge) is Active:
            active = edge
            rule = active.rule
            assert k == active.end > active.start, (k, active.end, active.start, active)
            if active.nextsym is None:
                # complete
                found = Found(rule.cat, active.lbl, active.start, k)
                newrule = Rule(rule.fun, found, rule.args)
                add_edge(found, found_chart[k][active.start], "complete", active)
                add_edge(newrule, dynrule_chart[found], "complete", active)

        elif type(edge) is Found:
            found = edge
            start = found.start
            assert k == found.end > start, (k, found.end, start, found)
            nextsym = Symbol(found.cat, found.lbl)
            # combine
            for active in active_chart[start][nextsym]:
                combine_inference_rule(active, found, sequences, active_chart, add_edge, "combine", active, found)

            # predict bottomup
            if bottomup:
                if not filtered:
                    for burule in grammar['bottomup'][nextsym]:
                        active = Active(start, start, burule.lbl, nextsym, 0, burule.rule)
                        combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred. BU", found)
                else:
                    predicts = predict_chart[start]
                    if predicts:
                        for burule in grammar['bottomup'][nextsym]:
                            if not predicts.isdisjoint(grammar['leftcorner'][burule.sym]):
                                active = Active(start, start, burule.lbl, nextsym, 0, burule.rule)
                                combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred. BU", found)

        else:
            assert type(edge) is Symbol or type(edge) is Rule, (type(edge), edge)

    # init-TD
    if k == 0:
        if topdown or filtered:
            # initial topdown predict
            for startcat in grammar['startcats']:
                for lbl in grammar['catlabels'][startcat]:
                    predict = Symbol(startcat, lbl)
                    add_edge(predict, predict_chart[k], "init TD")
    else:
        agenda.extend(active for nextsym, actives in active_chart[k].iteritems()
                      if type(nextsym) is Symbol for active in actives)

    # predict-item, predict-next, predict-TD
    while agenda:
        edge = agenda.pop()

        if type(edge) is Active:
            active = edge
            nextsym = active.nextsym
            assert k == active.end, (k, active.end, active)
            if type(nextsym) is Symbol:
                # predict item
                add_edge(nextsym, predict_chart[k], "pred. item", active)

        elif type(edge) is Symbol:
            predict = edge
            cat = predict.cat
            if type(cat) is Found:
                # predict next
                for rule in dynrule_chart[cat]:
                    assert cat == rule.cat, (cat, rule.cat)
                    add_active_edge(k, k, predict.lbl, 0, rule, sequences, active_chart, add_edge, "pred. next", rule, predict)

            elif topdown:
                if (not filtered
                    or k < len(tokens) and leftcorner_predict_token(predict, tokens[k], grammar)
                ):
                    # predict topdown
                    for rule in grammar['topdown'][cat]:
                        add_active_edge(k, k, predict.lbl, 0, rule, sequences, active_chart, add_edge, "pred. TD", predict)

        else:
            assert False, (type(edge), edge)



######################################################################
## Inference rules for parsing

def combine_inference_rule(active_edge, found, sequences, active_chart, add_edge, name, *antecedents):
    assert type(active_edge) == Active, (type(active_edge), active_edge)
    newrule = update_rule(active_edge.rule, active_edge.lbl, active_edge.pos, found, sequences)
    add_active_edge(active_edge.start, found.end, active_edge.lbl, active_edge.pos+1,
                    newrule, sequences, active_chart, add_edge, name, *antecedents)
    

def add_active_edge(i, k, lbl, p, rule, sequences, active_chart, add_edge, name, *antecedents):
    assert type(rule) == Rule, (type(rule), rule)
    rhs = sequences[rule.fun][lbl]
    if p < len(rhs):
        nextsym = rhs[p]
    else:
        nextsym = None
    if type(nextsym) is RHSSymbol:
        nextsym = nextsym.toSymbol(rule.args)
    newedge = Active(i, k, lbl, nextsym, p, rule)
    add_edge(newedge, active_chart[k][nextsym], name, *antecedents)


def update_rule(rule, lbl, p, newarg, sequences):
    argnr = sequences[rule.fun][lbl][p].arg
    newargs = rule.args[:argnr] + (newarg,) + rule.args[argnr+1:]
    return Rule(rule.fun, rule.cat, newargs)


def leftcorner_predict_token(predict, token, grammar):
    for sym in grammar['lcwords'][token]:
        if predict in grammar['leftcorner'][sym]:
            return True
    return False


######################################################################
## Helper classes and functions

Symbol = namedtuple("Symbol", "cat lbl")
Symbol.__str__ = lambda self: "<%s.%s>" % (self.cat, show_lbl(self.lbl))

RHSSymbol = namedtuple("RHSSymbol", "arg lbl")
RHSSymbol.toSymbol = lambda self, args: Symbol(args[self.arg], self.lbl)
RHSSymbol.__str__ = lambda self: "<%s.%s>" % (self.arg, show_lbl(self.lbl))

Found = namedtuple("Found", "cat lbl start end")
Found.__str__ = lambda self: "%s{%s:%s-%s}" % (self.cat, show_lbl(self.lbl), self.start, self.end)

Active = namedtuple("Active", "start end lbl nextsym pos rule")
Active.__str__ = lambda self: ("[%s-%s: %s = ... * %s/%s ... | %s]" % 
                               (self.start, self.end, self.lbl, self.nextsym, self.pos, self.rule))

Rule = namedtuple("Rule", "fun cat args")
Rule.__str__ = lambda self: "%s --> %s (%s)" % (self.cat, self.fun, ", ".join("%s" % (a,) for a in self.args))

BottomupRule = namedtuple("BottomupRule", "rule lbl sym")


NEFun = namedtuple("NEFun", "orig lbls")
NEFun.__str__ = lambda self: "%s/%s" % (self.orig, self.lbls)

NECat = namedtuple("NECat", "orig lbls")
NECat.__str__ = lambda self: "%s/%s" % (self.orig, self.lbls)

SFun = namedtuple("SFun", "orig args")
SFun.__str__ = lambda self: "%s[%s]" % (self.orig, ",".join("%s" % (a,) for a in self.args))


def get_orig(term):
    """
    Follows the 'orig' attribute until it comes to an object without that attribute.
    """
    while hasattr(term, 'orig'):
        term = term.orig
    return term


def objsize(obj):
    """
    Returns the size of a deeply nested object (dict/list/set).
    The size of each leaf (non-dict/list/set) is 1.
    """
    assert isinstance(obj, (dict, list, set)), obj
    if not obj:
        return 0
    if isinstance(obj, dict):
        obj = obj.values() 
    elem = next(iter(obj))
    if isinstance(elem, (dict, list, set)):
        return sum(objsize(v) for v in obj)
    else:
        return len(obj)


def powerset(seq, n=0):
    """
    A generator yielding all possible sublists of a given sequence.
    """
    if isinstance(seq, set):
        seq = list(seq)
    if n < len(seq):
        for item in powerset(seq, n+1):
            yield item
            yield [seq[n]] + item
    else:
        yield []


######################################################################
## Pretty-printing 

def print_chart(chart, tokens, startcats, sequences):
    """Print the final chart in MultiMarkdown format."""
    for k in range(1 + len(tokens)):
        predicted = chart[Symbol][k]
        found = set.union(*chart[Found][k])
        actives = set.union(*chart[Active][k].values())

        if k > 0:
            print '=== State %d: "%s" ===' % (k, tokens[k-1])
        else:
            print '=== State %d ===' % (k,)
        print
        print "Predicted:", ", ".join("%s" % (e,) for e in sorted(predicted))
        print "Found:", ", ".join("%s" % (e,) for e in sorted(found))
        print
        for edge in sorted(actives):
            print "|", show_active_edge(edge, sequences)
        print

    print "=== Dynamic rules ==="
    print
    for cat in sorted(chart[Rule]):
        for rule in sorted(chart[Rule][cat]):
            print "|", rule
    print

    print "=== Starting categories ==="
    print
    print ", ".join("%s" % (s,) for s in startcats)
    print


def trace_edge(name, edge, k, edgeid, sequences, antecedents):
    if type(edge) is Active:
        edgestr = show_active_edge(edge, sequences)
    elif type(edge) is Symbol:
        edgestr = "?%s :: P[%s]" % (edge, k)
    elif type(edge) is Found:
        assert k == edge.end, (k, edge.end, edge)
        edgestr = "[ %s.%s : %s ] :: F[%s,%s]" % (edge.cat, edge.lbl, edge, edge.start, edge.end)
    elif type(edge) is Rule:
        edgestr = "[ %s ] :: R[%s]" % (edge, k)
    if antecedents:
        name += " (%s)" % (",".join("%s" % a for a in antecedents),)
    print "%7s | %-20s| %s" % (edgeid, name, edgestr)


def show_active_edge(edge, sequences):
    rhs = sequences[edge.rule.fun][edge.lbl]
    return "[ %s : %s ; %s ] :: A[%s,%s]" % (show_lbl(edge.lbl), show_rhs(rhs, edge.pos), edge.rule, edge.start, edge.end)

def show_lbl(lbl):
    return ("r%d" if isinstance(lbl, int) else "%s") % (lbl,)

def show_sym(sym):
    return ('"%s"' if isinstance(sym, basestring) else "%s") % (sym,)

def show_rhs(rhs, p=None):
    rhs = map(show_sym, rhs)
    if p is not None:
        rhs = rhs[:p] + ["*"] + rhs[p:]
    return " ".join(rhs)


######################################################################
## Tracing

class TracedCounter(object):
    """
    A counter suitable for tracing. 

    At a given interval, it prints a "." to standard error.
    When the counter is finalized, it prints the final count
    and the number of seconds it took.

        >>> sys.stderr = sys.stdout
        >>> ctr = TracedCounter("Test counter", interval=2); \
            ctr.inc(); ctr.inc(); ctr.inc(); ctr.inc(); \
            ctr.inc(); ctr.inc(); ctr.inc(); ctr.inc(); \
            ctr.finalize()
        % Test counter.... [8] 0.00 s / 0.00 s
        >>> sys.stderr = sys.__stderr__
    """

    def __init__(self, title, interval=10000):
        sys.stderr.write("%% %s" % (title,))
        sys.stderr.flush()
        self.counter = 0
        self.starttime = time.time()
        self.startclock = time.clock()
        self.interval = interval

    def inc(self, out="."):
        self.counter += 1
        if self.counter % self.interval == 0:
            sys.stderr.write(out)
            sys.stderr.flush()

    def finalize(self):
        self.time = time.time() - self.starttime
        self.clock = time.clock() - self.startclock
        sys.stderr.write(" [%d] %.2f s / %.2f s\n" % (self.counter, self.clock, self.time))
        sys.stderr.flush()


######################################################################
## Testing the examples in docstrings

if __name__ == "__main__":
    import doctest
    doctest.testmod()
