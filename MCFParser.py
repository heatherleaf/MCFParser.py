
from collections import defaultdict, namedtuple
import sys
import time

class Parser(object):
    def __init__(self, mcfrules, startcats, trace=None, nonempty=None, **strategy):
        self._init_strategy(**strategy)
        if nonempty is None:
            nonempty = self.bottomup
        self._init_parser(startcats, trace)
        self._init_grammar(mcfrules)
        if self.grammar['is_empty'] and nonempty: 
            self._remove_emptyrules()
        if self.filtered:
            self._init_emptycats()
            self._init_leftcorner()
            # if self.grammar['is_empty']:
            #     self._init_emptyfollowers()
        # if self.bottomup and not self.filtered:
        #     self._init_emptycats()
        #     self._init_leftcorner()
        #     self._init_emptyfollowers()
        if self.bottomup:
            self._init_bu_grammar()
        if self.trace: 
            self.print_grammar_statistics()

    def print_grammar_statistics(self):
        print
        print "== Grammar statistics =="
        print "| Nr. terminals      | %7d |" % len(set(word for rhs in self.grammar['sequences'].itervalues()
                                                       for word in rhs if type(word) is not RHSSymbol))
        print "| Nr. nonterminals   | %7d |" % len(set(self.grammar['catlabels']))
        print "| Nr. nonterm-const. | %7d |" % objsize(self.grammar['catlabels'])
        print "| Nr. grammar rules  | %7d |" % objsize(self.grammar['topdown'])
        if 'emptyrules' in self.grammar:
            print "| Nr. empty rules    | %7d |" % objsize(self.grammar['emptyrules'])
        print "| Nr. constituents   | %7d |" % sum(len(self.grammar['sequences'][rule.fun]) 
                                                   for rules in self.grammar['topdown'].itervalues() 
                                                   for rule in rules)
        print "| Nr. const. lengths | %7d |" % sum(len(rhs) 
                                                   for rules in self.grammar['topdown'].itervalues() 
                                                   for rule in rules
                                                   for rhs in self.grammar['sequences'][rule.fun].itervalues())
        if 'emptycats' in self.grammar:
            print "| Nr. empty const.   | %7d |" % len(self.grammar['emptycats'])
        if 'leftcorner' in self.grammar:
            print "| Nr. leftc. pairs   | %7d |" % objsize(self.grammar['leftcorner'])
            print "| Nr. lcword. pairs  | %7d |" % objsize(self.grammar['lcwords'])
        print

    ######################################################################

    def _init_strategy(self, topdown=False, bottomup=False, filtered=False):
        strategy = (topdown, bottomup, filtered)
        error_types = [type(val).__name__ for val in strategy if not isinstance(val, bool)]
        if error_types:
            raise TypeError("Unexpected value type(s) for the parsing strategy: %s" % ", ".join(error_types))
        if not topdown and not bottomup:
            topdown = True
        if topdown and bottomup:
            raise ValueError("The parsing strategy cannot be both bottomup and topdown.")
        self.topdown = topdown
        self.bottomup = bottomup
        self.filtered = filtered

    def _init_parser(self, startcats, trace):
        self.trace = trace
        self.chart = {}
        self.statistics = {}
        self.grammar = {}
        if isinstance(startcats, basestring):
            startcats = [startcats]
        if not isinstance(startcats, (list, tuple, set)):
            raise TypeError("Unexpected type for starting categories: %s" % type(startcats).__name__)
        self.grammar['startcats'] = startcats

    def _remove_emptyrules(self):
        remove_emptyrules(self.grammar, self.trace)
        self.grammar['is_empty'] = not all(rhs for rhss in self.grammar['sequences'].itervalues() 
                                           for rhs in rhss.itervalues())

        assert not self.grammar['is_empty']
        assert all(not isinstance(cat, (list, set, dict)) and type(rule) is Rule 
                   for cat, rules in self.grammar['topdown'].iteritems() 
                   for rule in rules)

    def _init_grammar(self, mcfrules):
        td_grammar = self.grammar['topdown'] = defaultdict(list)
        catlabels = self.grammar['catlabels'] = {}
        sequences = self.grammar['sequences'] = {}
        is_empty = False
        if self.trace: ctr = TracedCounter("Topdown grammar:")

        for mcfrule in mcfrules:
            try: 
                fun, cat, args, rhss = mcfrule
            except ValueError:
                (fun, cat, args), rhss = mcfrule

            if not isinstance(args, (list, tuple)):
                raise TypeError("MCF rule %r: Rule arguments must be a list or a tuple of categories, "
                                "not %r" % (fun, type(args).__name))
            if any(isinstance(c, (list, set, dict)) for c in [cat] + list(args)):
                raise TypeError("MCF rule %r: Grammar category must not be a mutable object" % (fun,))

            if isinstance(rhss, (list, tuple)):
                rhsslist = list(enumerate(rhss))
            elif isinstance(rhss, dict):
                rhsslist = sorted(rhss.items())
            else:
                raise TypeError("MCF rule %r: Right-hand side must be a list, tuple or dict, "
                                "not %r" % (fun, type(rhss).__name__))
            if not rhsslist:
                raise ValueError("MCF rule %r: Empty right-hand side" % (fun,))

            lbltype = type(rhsslist[0][0])
            rhss = {}
            for lbl, rhs in rhsslist:
                if type(lbl) is not lbltype:
                    raise TypeError("MCF rule %r: Inconsistent label types in right-hand side: %r != %r" % 
                                    (fun, type(lbl).__name__, lbltype.__name__))
                if not isinstance(rhs, (list, tuple)):
                    raise TypeError("MCF rule %r: Right-hand side sequence must be a list or a tuple, " 
                                    "not %r" % (fun, type(rhs).__name__))
                rhss[lbl] = list(rhs)
                for n, sym in enumerate(rhss[lbl]):
                    if type(sym) is RHSSymbol:
                        pass
                    elif isinstance(sym, tuple):
                        if not (len(sym) == 2 and isinstance(sym[0], int) and type(sym[1]) is lbltype):
                            raise TypeError("MCF rule %r: Argument references in right-hand sides must be "
                                            "(%r,%r) tuples" % (fun, int.__name__, lbltype.__name__))
                        rhss[lbl][n] = RHSSymbol(*sym)
                    elif isinstance(sym, (list, dict, set)):
                        raise TypeError("MCF rule %r: Right-hand side symbols must be simple types, "
                                        "not %r" % (fun, type(sym).__name__))

            lbls = sorted(rhss.iterkeys())
            if cat not in catlabels:
                catlabels[cat] = lbls
            elif catlabels[cat] != lbls:
                raise ValueError("MCF rule %r: Inconsistent right-hand side labels for category %r" % (fun, cat))

            if fun not in sequences:
                sequences[fun] = rhss
            elif sequences[fun] != rhss:
                raise ValueError("MCF rule %r: Inconsistent right-hand-sides" % (fun,))

            rule = Rule(fun, cat, tuple(args))
            td_grammar[cat].append(rule)
            if self.trace: ctr.inc()

            if not all(rhss.itervalues()):
                is_empty = True

        if self.trace: ctr.finalize()
        self.grammar['is_empty'] = is_empty
        assert all(not isinstance(cat, (list, set, dict)) and type(rule) is Rule 
                   for cat, rules in self.grammar['topdown'].iteritems() for rule in rules)

    def _init_bu_grammar(self):
        td_grammar = self.grammar['topdown']
        sequences = self.grammar['sequences']
        bu_grammar = self.grammar['bottomup'] = defaultdict(list)
        if self.trace: ctr = TracedCounter("Bottomup grammar:")
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
                    bu_grammar[first].append((rule, lbl, Symbol(rule.cat, lbl)))
                    if self.trace: ctr.inc()
        if self.trace: ctr.finalize()
        assert all((type(first) is Symbol or not isinstance(first, (tuple, list, set, dict)))
                   and type(rule) is Rule and type(sym) is Symbol 
                   for first, burules in self.grammar['bottomup'].iteritems() 
                   for rule, lbl, sym in burules)

    def _init_emptycats(self):
        td_grammar = self.grammar['topdown']
        sequences = self.grammar['sequences']
        emptycats = self.grammar['emptycats'] = set()
        if not self.grammar['is_empty']:
            return
        if self.trace: ctr = TracedCounter("Empty categories:")
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
                    if self.trace: ctr.inc()
            elif type(rhs[pos]) is RHSSymbol:
                argsym = rhs[pos].toSymbol(rule.args)
                if argsym in emptycats:
                    agenda.append((pos + 1, rule, lbl))
                else:
                    empty_predicts[argsym].add((pos + 1, rule, lbl))
        if self.trace: ctr.finalize()
        assert all(type(sym) is Symbol for sym in emptycats)

    def _init_leftcorner(self):
        td_grammar = self.grammar['topdown']
        sequences = self.grammar['sequences']
        emptycats = self.grammar['emptycats'] 
        leftcorner_words = self.grammar['lcwords'] = defaultdict(set)
        leftcorner = self.grammar['leftcorner'] = defaultdict(set)

        if self.trace: ctr = TracedCounter("Leftcorners:")
        leftcorner_parents = defaultdict(set)
        for tdrules in td_grammar.itervalues():
            for rule in tdrules:
                rhss = sequences[rule.fun]
                for lbl, rhs in rhss.iteritems():
                    parent = Symbol(rule.cat, lbl)
                    for sym in rhs:
                        if self.trace: ctr.inc()
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
                    if self.trace: ctr.inc()
                    if leftcorner[parent]:
                        leftcorner[sym].update(leftcorner[parent])
                    elif parent in leftcorner_parents:
                        agenda.extend(leftcorner_parents[parent])

        for (cat, lbls) in self.grammar['catlabels'].iteritems():
            for lbl in lbls:
                sym = Symbol(cat, lbl)
                leftcorner[sym].add(sym)
                if self.trace: ctr.inc()
        if self.trace: ctr.finalize()

        assert all(type(first) is Symbol and type(parent) is Symbol 
                   for first, parents in self.grammar['leftcorner'].iteritems() 
                   for parent in parents)
        assert all(not isinstance(word, (tuple, list, set, dict)) and type(parent) is Symbol
                   for word, parents in self.grammar['lcwords'].iteritems()
                   for parent in parents)

    def _init_emptyfollowers(self):
        emptyfollowers = self.grammar['emptyfollowers'] = defaultdict(set)
        if self.trace: ctr = TracedCounter("Empty followers:")
        td_grammar = self.grammar['topdown']
        sequences = self.grammar['sequences']
        emptycats = self.grammar['emptycats'] 
        leftcorner = self.grammar['leftcorner']
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
                                if self.trace: ctr.inc()

        # for after, parents in leftcorner.iteritems():
        #     for parent in parents:
        #         for before in direct_predecessors[parent]:
        #             emptyfollowers[before].add(after)
        #             if self.trace: ctr.inc()
        # if self.trace: ctr.finalize()

        assert all(type(before) is Symbol and before in emptycats 
                   for before, afters in emptyfollowers.iteritems() for after in afters)

    ######################################################################

    def parse(self, tokens, n=None, trace=None):
        self.chart_parse(tokens, trace)
        return self.extract_trees(n=n)

    def init_chart(self, tokens):
        assert isinstance(tokens, (list, tuple)), "Tokens must be a list or a tuple of strings"
        self.tokens = tokens
        self.positions = range(1 + len(tokens))
        self.chart[Active] = [defaultdict(set) for _ in self.positions]
        self.chart[Found] = [[set() for _ in self.positions] for _ in self.positions]
        self.chart[Rule] = defaultdict(set)
        if self.grammar['is_empty']:
            self.chart[Symbol] = [defaultdict(set) for _ in self.positions]
        else:
            self.chart[Symbol] = [set() for _ in self.positions]
        self.statistics['Time'] = 0.0
        self.statistics['Chart'] = defaultdict(int) 
        self.statistics['Inferences'] = defaultdict(int)

    def chart_parse(self, tokens, trace=None):
        if trace is None: trace = self.trace
        self.init_chart(tokens)
        if trace == 1: 
            ctr = TracedCounter("Parse: ", interval=1) # TODO: print strategy
        elif trace > 1:
            print '\n== Parsing: "%s" ==\n' % (" ".join(tokens),)
        for k in self.positions:
            if k > 0 and trace == 1: ctr.inc(tokens[k-1][0])
            self.process_token(k, trace)
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

    def print_parse_statistics(self):
        print "== Parse statistics =="
        print "||            |",
        statkeys = [set(stat) for stat in self.statistics.itervalues() if isinstance(stat, dict)]
        statkeys = sorted(set.union(*statkeys))
        for key in statkeys: print "%8s |" % (key,),
        print
        for hdr, stat in self.statistics.iteritems():
            if isinstance(stat, dict):
                print "| %-10s  |" % (hdr,),
                for key in statkeys: 
                    print "%8s |" % (stat.get(key, "--"),),
                print
        for hdr, value in self.statistics.iteritems():
            if not isinstance(value, dict):
                print "| %-10s  |" % (hdr,),
                value = "%s" % (value,)
                print value, " " * (10 * len(statkeys) - len(value)), "|" * len(statkeys)

    def process_token(self, k, trace=None):
        if trace is None: trace = self.trace
        process_token(k, self.tokens, self.chart, self.statistics, self.grammar,
                      topdown=self.topdown, bottomup=self.bottomup, filtered=self.filtered, trace=trace)

    def extract_trees(self, startcats=None, start=0, end=None, n=None):
        if end is None:
            end = len(self.tokens)
        if startcats is None:
            startcats = self.grammar['startcats']
        emptyrules = self.grammar.get('emptyrules', {})
        ctr = 0
        for cat in startcats:
            for lbl in self.grammar['catlabels'][cat]:
                topcat = Found(cat, lbl, start, end)
                for tree in generate_trees(topcat, self.chart[Rule], emptyrules=emptyrules, visited=set()):
                    yield tree
                    ctr += 1
                    if n and ctr >= n: 
                        return

    def print_chart(self):
        print_chart(self.chart, self.tokens, self.grammar['startcats'], self.grammar['sequences'])


######################################################################

def remove_emptyrules(grammar, trace=None):
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
                                                       sym[0] in xnrs and sym[1] in elbls)])
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

    if trace: ctr.finalize()


def remove_emptyrules_alternative(grammar, trace=None):
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

    if trace: ctr.finalize()


# remove_emptyrules = remove_emptyrules_alternative


######################################################################

def generate_trees(cat, rules, emptyrules={}, visited=set()):
    catrules = rules.get(cat)
    if not catrules: 
        cat = get_orig(cat)
        catrules = emptyrules.get(cat, ())
        rules, emptyrules = emptyrules, {}
    for rule in catrules:
        if rule not in visited:
            visited_copy = visited | set([rule])
            assert rule.cat == cat, (cat, rule)
            fun = get_orig(rule.fun)
            for argtrees in generate_tree_children(0, rule.args, rules, emptyrules, visited_copy):
                yield (fun,) + argtrees

def generate_tree_children(nr, args, rules, emptyrules, visited):
    if nr >= len(args): 
        yield ()
    else:
        for argtree in generate_trees(args[nr], rules, emptyrules, visited):
            for resttrees in generate_tree_children(nr+1, args, rules, emptyrules, visited):
                yield (argtree,) + resttrees


######################################################################

def process_token(k, tokens, chart, statistics, grammar, topdown=True, bottomup=False, filtered=False, trace=None):
    assert bool(topdown) != bool(bottomup), "Parsing should be either topdown or bottomup"
    if trace > 1:
        if k > 0:
            print '=== State %d: "%s" ===' % (k, tokens[k-1])
        else:
            print '=== State %d ===' % (k,)

    agenda = []
    if trace is None or trace is False:
        def add_edge(edge, edgeset, name, *antecedents):
            if edge not in edgeset:
                edgeset.add(edge)
                agenda.append(edge)
    else:
        chart.setdefault('edgecounter', 0)
        chart.setdefault('edgenumbers', {})
        def add_edge(edge, edgeset, name, *antecedents):
            statistics['Inferences'][type(edge).__name__] += 1
            if edge not in edgeset:
                edgeset.add(edge)
                agenda.append(edge)
                statistics['Chart'][type(edge).__name__] += 1
                if trace > 1: 
                    chart['edgecounter'] += 1
                    chart['edgenumbers'][edge] = chart['edgecounter']
                    antecedents = [chart['edgenumbers'][ant] for ant in antecedents]
                    trace_edge(name, k, edge, chart['edgecounter'], grammar['sequences'], antecedents)

    starttime = time.clock()
    if grammar['is_empty']:
        process_token_emptygrammar(k, tokens, chart, grammar, agenda, add_edge, topdown, bottomup, filtered)
    else:
        process_token_nonempty(k, tokens, chart, grammar, agenda, add_edge, topdown, bottomup, filtered)
    statistics['Time'] += time.clock() - starttime

    if trace > 1:
        print

######################################################################
## parsing grammars with epsilon rules

def process_token_emptygrammar(k, tokens, chart, grammar, agenda, add_edge, topdown, bottomup, filtered):
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
            (i, _j, lbl, _, p, rule) = active
            assert _j == k-1
            add_active_edge(i, k, lbl, p+1, rule, sequences, active_chart, add_edge, "scan", active)

        if bottomup:
            # scan bottomup 
            if not filtered:
                for (rule, lbl, _sym) in grammar['bottomup'][tokens[k-1]]:
                    add_active_edge(k-1, k, lbl, 1, rule, sequences, active_chart, add_edge, "scan BU")
            else:
                predicts = predict_chart[k-1]
                if predicts:
                    for (rule, lbl, sym) in grammar['bottomup'][tokens[k-1]]:
                        if not predicts.isdisjoint(grammar['leftcorner'][sym]):
                            add_active_edge(k-1, k, lbl, 1, rule, sequences, active_chart, add_edge, "scan BU")

    if bottomup and not filtered:
        # scan epsilon
        for (rule, lbl, _sym) in grammar['bottomup'][None]:
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
            add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "scan empty")

    # process agenda
    while agenda:
        edge = agenda.pop()
        if type(edge) is Active:
            j, _k, lbl, nextsym, p, rule = active = edge
            assert _k == k
            fun, cat, args = rule
            if nextsym is None:
                # complete
                found = Found(cat, lbl, j, k)
                newrule = Rule(fun, found, args)
                add_edge(found, found_chart[k][j], "complete", active)
                add_edge(newrule, dynrule_chart[found], "complete", active)

            elif type(nextsym) is Symbol:
                nextcat, nextlbl = nextsym
                # predict item
                add_edge(nextsym, predict_chart[k][nextcat], "pred. item", active)
                # combine
                found = Found(nextcat, nextlbl, k, k)
                if found in found_chart[k][k]:
                    assert k == found[-1]
                    combine_inference_rule(active, found, sequences, active_chart, add_edge, "combine", active, found)

        elif type(edge) is Rule:
            # predict next
            _fun, cat, _args = rule = edge
            assert cat[-1] == k
            for predict in predict_chart[k][cat]:
                assert cat == predict.cat
                add_active_edge(k, k, predict.lbl, 0, rule, sequences, active_chart, add_edge, "pred. next", rule, predict)

        elif type(edge) is Symbol:
            cat, lbl = predict = edge
            if type(cat) is Found:
                # predict next
                for rule in dynrule_chart[cat]:
                    assert cat == rule.cat
                    add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "pred. next", rule, predict)

            elif topdown:
                if (not filtered
                    or predict in grammar['emptycats']
                    or k < len(tokens) and any(predict in grammar['leftcorner'][sym]
                                               for sym in grammar['lcwords'][tokens[k]])
                ):
                    # predict topdown
                    for rule in grammar['topdown'][cat]:
                        add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "pred. TD", predict)

            elif bottomup and filtered:
                # scan epsilon
                for (rule, lbl, sym) in grammar['bottomup'][None]:
                    if predict in grammar['leftcorner'][sym]:
                        add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "scan empty", predict)

                # predict bottomup
                for found in found_chart[k][k]:
                    nextcat, nextlbl, _j, _k = found
                    assert _j == _k == k
                    nextsym = Symbol(nextcat, nextlbl)
                    for (rule, lbl, sym) in grammar['bottomup'][nextsym]:
                        if predict in grammar['leftcorner'][sym]:
                            active = Active(k, k, lbl, nextsym, 0, rule)
                            combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred. BU", predict, found)

        elif type(edge) is Found:
            argcat, arglbl, j, _k = found = edge
            assert _k == k
            nextsym = (argcat, arglbl)
            # combine
            for active in active_chart[j][nextsym]:
                combine_inference_rule(active, found, sequences, active_chart, add_edge, "combine", active, found)

            if bottomup:
                # predict bottomup
                if not filtered:
                    for (rule, lbl, _sym) in grammar['bottomup'][nextsym]:
                        active = Active(j, j, lbl, nextsym, 0, rule)
                        combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred. BU", found)
                else:
                    predicts = predict_chart[j]
                    if predicts:
                        if j == k:
                            predicts = set.union(*predicts.itervalues())
                        for (rule, lbl, sym) in grammar['bottomup'][nextsym]:
                            if not predicts.isdisjoint(grammar['leftcorner'][sym]):
                                active = Active(j, j, lbl, nextsym, 0, rule)
                                combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred. BU", found)

        else:
            assert False, (type(edge), edge)

    predict_chart[k] = set().union(*predict_chart[k].itervalues())




######################################################################
## parsing grammars with no epsilon rules

def process_token_nonempty(k, tokens, chart, grammar, agenda, add_edge, topdown, bottomup, filtered):
    sequences = grammar['sequences']
    active_chart = chart[Active]
    predict_chart = chart[Symbol]
    found_chart = chart[Found]
    dynrule_chart = chart[Rule]

    # scan, scan-BU
    if k > 0:
        # scan
        for active in active_chart[k-1][tokens[k-1]]:
            (i, _j, lbl, _, p, rule) = active
            assert _j == k-1
            add_active_edge(i, k, lbl, p+1, rule, sequences, active_chart, add_edge, "scan", active)

        if bottomup:
            # scan bottomup 
            if not filtered:
                for (rule, lbl, _sym) in grammar['bottomup'][tokens[k-1]]:
                    add_active_edge(k-1, k, lbl, 1, rule, sequences, active_chart, add_edge, "scan BU")
            else:
                predicts = predict_chart[k-1]
                if predicts:
                    for (rule, lbl, sym) in grammar['bottomup'][tokens[k-1]]:
                        if not predicts.isdisjoint(grammar['leftcorner'][sym]):
                            add_active_edge(k-1, k, lbl, 1, rule, sequences, active_chart, add_edge, "scan BU")

    # complete, combine, predict-BU
    while agenda:
        edge = agenda.pop()

        if type(edge) is Active:
            j, _k, lbl, nextsym, p, rule = active = edge
            assert j < _k == k
            fun, cat, args = rule
            if nextsym is None:
                # complete
                found = Found(cat, lbl, j, k)
                newrule = Rule(fun, found, args)
                add_edge(found, found_chart[k][j], "complete", active)
                add_edge(newrule, dynrule_chart[found], "complete", active)

        elif type(edge) is Found:
            argcat, arglbl, j, _k = found = edge
            assert j < _k == k
            nextsym = Symbol(argcat, arglbl)
            # combine
            for active in active_chart[j][nextsym]:
                combine_inference_rule(active, found, sequences, active_chart, add_edge, "combine", active, found)

            # predict bottomup
            if bottomup:
                if not filtered:
                    for (rule, lbl, _sym) in grammar['bottomup'][nextsym]:
                        active = Active(j, j, lbl, nextsym, 0, rule)
                        combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred. BU", found)
                else:
                    predicts = predict_chart[j]
                    if predicts:
                        for (rule, lbl, sym) in grammar['bottomup'][nextsym]:
                            if not predicts.isdisjoint(grammar['leftcorner'][sym]):
                                active = Active(j, j, lbl, nextsym, 0, rule)
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
            j, _k, lbl, nextsym, p, rule = active = edge
            assert _k == k
            if type(nextsym) is Symbol:
                # predict item
                add_edge(nextsym, predict_chart[k], "pred. item", active)

        elif type(edge) is Symbol:
            cat, lbl = predict = edge
            if type(cat) is Found:
                # predict next
                for rule in dynrule_chart[cat]:
                    assert cat == rule.cat
                    add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "pred. next", rule, predict)

            elif topdown:
                if (not filtered
                    or predict in grammar['emptycats']
                    or k < len(tokens) and any(predict in grammar['leftcorner'][sym]
                                               for sym in grammar['lcwords'][tokens[k]])
                ):
                    # predict topdown
                    for rule in grammar['topdown'][cat]:
                        add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "pred. TD", predict)

        else:
            assert False, (type(edge), edge)



######################################################################
## basic inference rules


def combine_inference_rule(active_edge, found, sequences, active_chart, add_edge, name, *antecedents):
    assert type(active_edge) == Active, (active_edge, type(active_edge))
    i, j, lbl, _, p, rule = active_edge
    newrule = update_rule(rule, lbl, p, found, sequences)
    k = found[-1]
    add_active_edge(i, k, lbl, p+1, newrule, sequences, active_chart, add_edge, name, *antecedents)
    

def add_active_edge(i, k, lbl, p, rule, sequences, active_chart, add_edge, name, *antecedents):
    assert type(rule) == Rule, (rule, type(rule))
    fun, _cat, args = rule
    rhs = sequences[fun][lbl]
    if p < len(rhs):
        nextsym = rhs[p]
    else:
        nextsym = None
    if type(nextsym) is RHSSymbol:
        nextsym = nextsym.toSymbol(args)
    newedge = Active(i, k, lbl, nextsym, p, rule)
    add_edge(newedge, active_chart[k][nextsym], name, *antecedents)


def update_rule(rule, lbl, p, newarg, sequences):
    fun, cat, args = rule
    argnr, _arglbl = sequences[fun][lbl][p]
    newargs = args[:argnr] + (newarg,) + args[argnr+1:]
    return Rule(fun, cat, newargs)



######################################################################
## helper classes and functions

Symbol = namedtuple("Symbol", "cat lbl")
RHSSymbol = namedtuple("RHSSymbol", "arg lbl")
RHSSymbol.toSymbol = lambda self, args: Symbol(args[self.arg], self.lbl)

Symbol.__str__ = lambda self: "<%s.%s>" % self
RHSSymbol.__str__ = lambda self: "<%s.%s>" % self

Found = namedtuple("Found", "cat lbl start end")
Active = namedtuple("Active", "start end lbl nextsym pos rule")
Rule = namedtuple("Rule", "fun cat args")

Found.__str__ = lambda self: "%s{%s:%s-%s}" % self
Active.__str__ = lambda self: "[%s-%s: %s = ... * %s/%s ... | %s]" % self
Rule.__str__ = lambda self: "%s --> %s (%s)" % (self.cat, self.fun, ", ".join("%s" % (a,) for a in self.args))

NEFun = namedtuple("NEFun", "orig lbls")
NECat = namedtuple("NECat", "orig lbls")
SFun = namedtuple("SFun", "orig args")

NEFun.__str__ = lambda self: "%s/%s" % self
NECat.__str__ = lambda self: "%s/%s" % self
SFun.__str__ = lambda self: "%s[%s]" % (self.orig, ",".join("%s" % (a,) for a in self.args))


def get_orig(term):
    while hasattr(term, 'orig'):
        term = term.orig
    return term


def objsize(obj):
    if isinstance(obj, dict):
        return sum(objsize(v) for v in obj.itervalues())
    elif isinstance(obj, (list, set)):
        return sum(objsize(v) for v in obj)
    else:
        return 1


def powerset(seq, n=0):
    if isinstance(seq, set):
        seq = list(seq)
    if n < len(seq):
        for item in powerset(seq, n+1):
            yield item
            yield [seq[n]] + item
    else:
        yield []


class TracedCounter(object):
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
## pretty-printing 

def print_chart(chart, tokens, startcats, sequences):
    for k in range(1 + len(tokens)):
        predicted = chart[Symbol][k]
        found = set.union(*chart[Found][k].values())
        actives = set.union(*chart[Active][k].values())

        if k > 0:
            print '=== State %d: "%s" ===' % (k, tokens[k-1])
        else:
            print '=== State %d ===' % (k,)
        print
        print "Predicted:", ", ".join("%s" % e for e in sorted(predicted))
        print "Found:", ", ".join("%s" % e for e in sorted(found))
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
    print ", ".join("%s" % s for s in startcats)
    print


def trace_edge(name, k, edge, edgenr, sequences, antecedents):
    if type(edge) is Active:
        edgestr = show_active_edge(edge, sequences)
    elif type(edge) is Symbol:
        edgestr = "?%s :: P_%s" % (edge, k)
    elif type(edge) is Found:
        cat, lbl, j, _k = edge
        assert _k == k, edge
        edgestr = "[ %s.%s : %s ] :: F_%s,%s" % (cat, lbl, edge, j, k)
    elif type(edge) is Rule:
        edgestr = "[ %s ] :: R_%s" % (edge, k)
    if antecedents:
        name += " (%s)" % (",".join("%s" % a for a in antecedents),)
    print "|  %6s | %-10s  | %s" % (edgenr, name, edgestr)


def show_active_edge(edge, sequences):
    i, k, lbl, nextsym, p, rule = edge
    fun, _cat, _args = rule
    rhs = sequences[fun][lbl]
    rhs = rhs[:p] + ["*"] + rhs[p:]
    rhsstr = " ".join("%s" % (s,) for s in rhs)
    return "[ %s : %s ; %s ] :: A_%s,%s" % (lbl, rhsstr, rule, i, k)

