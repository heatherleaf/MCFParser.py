
from collections import defaultdict, namedtuple
import sys
import time

class TracedCounter(object):
    def __init__(self, title, interval=10000):
        print "#", title,
        sys.stdout.flush()
        self.counter = 0
        self.starttime = time.time()
        self.startclock = time.clock()
        self.interval = interval

    def inc(self, out="."):
        self.counter += 1
        if self.counter % self.interval == 0:
            sys.stdout.write(out)
            sys.stdout.flush()

    def finalize(self):
        self.time = time.time() - self.starttime
        self.clock = time.clock() - self.startclock
        print " [%d] %.2f s / %.2f s" % (self.counter, self.clock, self.time)


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
            print "# Nr. terminals:     ", len(set(word for rhs in self.grammar['sequences'].itervalues()
                                                   for word in rhs if type(word) is not RHSSymbol))
            print "# Nr. nonterminals:  ", len(set(self.grammar['catlabels']))
            print "# Nr. nonterm-const.:", sum(len(lbls) for lbls in self.grammar['catlabels'].itervalues())
            print "# Nr. grammar rules: ", sum(len(rules) for rules in self.grammar['topdown'].itervalues())
            print "# Nr. constituents:  ", sum(len(self.grammar['sequences'][rule.fun]) 
                                               for rules in self.grammar['topdown'].itervalues() for rule in rules)
            print "# Nr. const. lengths:", sum(len(rhs) 
                                               for rules in self.grammar['topdown'].itervalues() for rule in rules
                                               for rhs in self.grammar['sequences'][rule.fun].itervalues())
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
        td_grammar = self.grammar['topdown'] 
        sequences = self.grammar['sequences'] 

        emptyrules = remove_emptyrules(self.grammar, self.trace)
        self.grammar['emptyrules'] = emptyrules
        self.grammar['catlabels'] = dict((cat, sorted(sequences[rules[0].fun])) 
                                         for cat, rules in td_grammar.iteritems()) 
        self.grammar['is_empty'] = False

        assert not self.grammar['is_empty']
        assert all(rhs for rhss in sequences.itervalues() for rhs in rhss.itervalues())
        assert all(not isinstance(cat, (list, set, dict)) and type(rule) is Rule 
                   for cat, rules in td_grammar.iteritems() for rule in rules)

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
        if self.trace: ctr = TracedCounter("Empty categoriess:")
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
        if trace == 1: ctr = TracedCounter("Parse: ", interval=1) # TODO: print strategy
        for k in self.positions:
            if k > 0 and trace == 1: ctr.inc(tokens[k-1][0])
            self.process_token(k, trace)
        if trace == 1: ctr.finalize()
        for key in ('Chart', 'Inferences'):
            stat = self.statistics[key]
            stat['TOTAL'] = sum(stat[key] for key in stat if key != 'TOTAL')
            if trace > 1:
                print "# %s = {%s}" % (key, ", ".join("%s:%s" % kv for kv in sorted(stat.items())))
        if trace > 1:
            print "# TIME = %.2f s" % self.statistics['Time']
        return any(Found(startcat, lbl, 0, len(tokens)) in self.chart[Rule]
                   for startcat in self.grammar['startcats']
                   for lbl in self.grammar['catlabels'][startcat])

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
    oldrules = grammar['topdown']
    sequences = grammar['sequences']
    empty_rules = defaultdict(set)
    cats = set()
    agenda = set()
    argrules = defaultdict(lambda:defaultdict(set))
    newrules = defaultdict(set)

    for cat in oldrules:
        cats.add(cat)
        newrules[cat] = set(oldrules[cat])
        for rule in newrules[cat]:
            rhss = sequences[rule.fun]
            if not all(rhss.itervalues()):
                agenda.add(rule)
            for argnr, arg in enumerate(rule.args):
                argrules[arg][rule].add(argnr)

    while agenda:
        rule = agenda.pop()
        rhss = sequences[rule.fun]
        assert rule.fun not in empty_rules[rule.cat], rule
        empty_rules[rule.cat].add(rule)

        elbls = set(lbl for lbl, rhs in rhss.iteritems() if not rhs)
        elblstr = repr(sorted(elbls))
        newfun = NEFun(rule.fun, elblstr)
        assert type(rule.fun) is not NEFun, newfun
        newcat = NECat(rule.cat, elblstr)
        assert type(rule.cat) is not NECat, newfun
        newrule = Rule(newfun, newcat, rule.args)
        assert newrule not in newrules[newcat], newrule
        newrules[newcat].add(newrule)
        if trace: ctr.inc()

        newrhss = dict((lbl, rhs) for (lbl, rhs) in rhss.iteritems() if rhs)
        if newfun in sequences:
            assert sequences[newfun] == newrhss
        else:
            sequences[newfun] = newrhss
        if not newrhss:
            empty_rules[newcat].add(newrule)

        if newcat not in cats:
            cats.add(newcat)
            for xrule, xnrs in argrules[rule.cat].iteritems():
                newxcat = xrule.cat
                newxargs = tuple(newcat if xnr in xnrs else xarg 
                                 for (xnr, xarg) in enumerate(xrule.args))
                if type(xrule.fun) is SFun: 
                    newxfun = SFun(xrule.fun.orig, newxargs)
                else:
                    newxfun = SFun(xrule.fun, newxargs)
                newxrule = Rule(newxfun, newxcat, newxargs)
                assert type(newxfun.orig) not in (SFun, NEFun), newxrule
                assert newxrule not in newrules[newxcat], newxrule
                newrules[newxcat].add(newxrule)
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

    for erules in empty_rules.itervalues():
        for erule in erules:
            newrules[erule.cat].remove(erule)
            if erule.fun in sequences:
                del sequences[erule.fun]

    oldrules.clear()
    for cat, rules in newrules.iteritems():
        if rules:
            oldrules[cat] = list(rules)

    if trace: ctr.finalize()
    return empty_rules

NEFun = namedtuple("NEFun", "orig elbls")
NECat = namedtuple("NECat", "orig elbls")
SFun = namedtuple("SFun", "orig args")

NEFun.__str__ = lambda self: "%s/%s" % self
NECat.__str__ = lambda self: "%s/%s" % self
SFun.__str__ = lambda self: "%s[%s]" % (self.orig, ",".join("%s" % (a,) for a in self.args))


######################################################################

def generate_trees(cat, rules, emptyrules={}, visited=set()):
    while type(cat) is NECat:
        cat = cat.orig
    catrules = rules.get(cat)
    if not catrules: 
        catrules = emptyrules.get(cat, ())
    for rule in catrules:
        if rule not in visited:
            visited_copy = visited | set([rule])
            assert rule.cat == cat, (cat, rule)
            fun = rule.fun
            while type(fun) in (SFun, NEFun):
                fun = fun.orig
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
        print "###", k, tokens[k-1] if k > 0 else "--START--"

    agenda = []
    if trace is None or trace is False:
        def add_edge(edge, chart, name):
            if edge not in chart:
                chart.add(edge)
                agenda.append(edge)
    else:
        def add_edge(edge, chart, name):
            statistics['Inferences'][type(edge).__name__] += 1
            if edge not in chart:
                chart.add(edge)
                agenda.append(edge)
                statistics['Chart'][type(edge).__name__] += 1
                if trace > 1: 
                    trace_edge(name, edge, grammar['sequences'])

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
                    add_edge(predict, predict_chart[k][startcat], "initial-TD")

    else:
        # scan
        for (i, _j, lbl, _, p, rule) in active_chart[k-1][tokens[k-1]]:
            assert _j == k-1
            add_active_edge(i, k, lbl, p+1, rule, sequences, active_chart, add_edge, "scan")

        if bottomup:
            # scan bottomup 
            if not filtered:
                for (rule, lbl, _sym) in grammar['bottomup'][tokens[k-1]]:
                    add_active_edge(k-1, k, lbl, 1, rule, sequences, active_chart, add_edge, "scan-BU")
            else:
                predicts = predict_chart[k-1]
                if predicts:
                    for (rule, lbl, sym) in grammar['bottomup'][tokens[k-1]]:
                        if not predicts.isdisjoint(grammar['leftcorner'][sym]):
                            add_active_edge(k-1, k, lbl, 1, rule, sequences, active_chart, add_edge, "scan-BU")

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
            add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "scan-BUE")

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
                add_edge(found, found_chart[k][j], "comp-pred")
                add_edge(newrule, dynrule_chart[found], "comp-rule")

            elif type(nextsym) is Symbol:
                nextcat, nextlbl = nextsym
                # predict item
                add_edge(nextsym, predict_chart[k][nextcat], "pred-item")
                # combine
                found = Found(nextcat, nextlbl, k, k)
                if found in found_chart[k][k]:
                    assert k == found[-1]
                    combine_inference_rule(active, found, sequences, active_chart, add_edge, "cmbn-act")

        elif type(edge) is Rule:
            # predict next
            _fun, cat, _args = rule = edge
            assert cat[-1] == k
            for _cat, lbl in predict_chart[k][cat]:
                assert _cat == cat
                add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "next-rule")

        elif type(edge) is Symbol:
            cat, lbl = predict = edge
            if type(cat) is Found:
                # predict next
                for rule in dynrule_chart[cat]:
                    assert cat == rule.cat
                    add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "next-pred")

            elif topdown:
                if (not filtered
                    or predict in grammar['emptycats']
                    or k < len(tokens) and any(predict in grammar['leftcorner'][sym]
                                               for sym in grammar['lcwords'][tokens[k]])
                ):
                    # predict topdown
                    for rule in grammar['topdown'][cat]:
                        add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "pred-TD")

            elif bottomup and filtered:
                # scan epsilon
                for (rule, lbl, sym) in grammar['bottomup'][None]:
                    if predict in grammar['leftcorner'][sym]:
                        add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "scan-eps")

                # predict bottomup
                for found in found_chart[k][k]:
                    nextcat, nextlbl, _j, _k = found
                    assert _j == _k == k
                    nextsym = Symbol(nextcat, nextlbl)
                    for (rule, lbl, sym) in grammar['bottomup'][nextsym]:
                        if predict in grammar['leftcorner'][sym]:
                            active = Active(k, k, lbl, nextsym, 0, rule)
                            combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred-BU-?")

        elif type(edge) is Found:
            argcat, arglbl, j, _k = found = edge
            assert _k == k
            nextsym = (argcat, arglbl)
            # combine
            for active in active_chart[j][nextsym]:
                combine_inference_rule(active, found, sequences, active_chart, add_edge, "cmbn-pass")

            if bottomup:
                # predict bottomup
                if not filtered:
                    for (rule, lbl, _sym) in grammar['bottomup'][nextsym]:
                        active = Active(j, j, lbl, nextsym, 0, rule)
                        combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred-BU")
                else:
                    predicts = predict_chart[j]
                    if predicts:
                        if j == k:
                            predicts = set.union(*predicts.itervalues())
                        for (rule, lbl, sym) in grammar['bottomup'][nextsym]:
                            if not predicts.isdisjoint(grammar['leftcorner'][sym]):
                                active = Active(j, j, lbl, nextsym, 0, rule)
                                combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred-BU-!")

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
        for (i, _j, lbl, _, p, rule) in active_chart[k-1][tokens[k-1]]:
            assert _j == k-1
            add_active_edge(i, k, lbl, p+1, rule, sequences, active_chart, add_edge, "scan")

        if bottomup:
            # scan bottomup 
            if not filtered:
                for (rule, lbl, _sym) in grammar['bottomup'][tokens[k-1]]:
                    add_active_edge(k-1, k, lbl, 1, rule, sequences, active_chart, add_edge, "scan-BU")
            else:
                predicts = predict_chart[k-1]
                if predicts:
                    for (rule, lbl, sym) in grammar['bottomup'][tokens[k-1]]:
                        if not predicts.isdisjoint(grammar['leftcorner'][sym]):
                            add_active_edge(k-1, k, lbl, 1, rule, sequences, active_chart, add_edge, "scan-BU")

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
                add_edge(found, found_chart[k][j], "comp-pred")
                add_edge(newrule, dynrule_chart[found], "comp-rule")

        elif type(edge) is Found:
            argcat, arglbl, j, _k = found = edge
            assert j < _k == k
            nextsym = Symbol(argcat, arglbl)
            # combine
            for active in active_chart[j][nextsym]:
                combine_inference_rule(active, found, sequences, active_chart, add_edge, "cmbn-pass")

            # predict bottomup
            if bottomup:
                if not filtered:
                    for (rule, lbl, _sym) in grammar['bottomup'][nextsym]:
                        active = Active(j, j, lbl, nextsym, 0, rule)
                        combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred-BU")
                else:
                    predicts = predict_chart[j]
                    if predicts:
                        for (rule, lbl, sym) in grammar['bottomup'][nextsym]:
                            if not predicts.isdisjoint(grammar['leftcorner'][sym]):
                                active = Active(j, j, lbl, nextsym, 0, rule)
                                combine_inference_rule(active, found, sequences, active_chart, add_edge, "pred-BU-!")

        else:
            assert type(edge) is Symbol or type(edge) is Rule, (type(edge), edge)

    # init-TD
    if k == 0:
        if topdown or filtered:
            # initial topdown predict
            for startcat in grammar['startcats']:
                for lbl in grammar['catlabels'][startcat]:
                    predict = Symbol(startcat, lbl)
                    add_edge(predict, predict_chart[k], "initial-TD")
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
                add_edge(nextsym, predict_chart[k], "pred-item")

        elif type(edge) is Symbol:
            cat, lbl = predict = edge
            if type(cat) is Found:
                # predict next
                for rule in dynrule_chart[cat]:
                    assert cat == rule.cat
                    add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "next-pred")

            elif topdown:
                if (not filtered
                    or predict in grammar['emptycats']
                    or k < len(tokens) and any(predict in grammar['leftcorner'][sym]
                                               for sym in grammar['lcwords'][tokens[k]])
                ):
                    # predict topdown
                    for rule in grammar['topdown'][cat]:
                        add_active_edge(k, k, lbl, 0, rule, sequences, active_chart, add_edge, "pred-TD")

        else:
            assert False, (type(edge), edge)



######################################################################
## basic inference rules


def combine_inference_rule(active_edge, found, sequences, active_chart, add_edge, name):
    assert type(active_edge) == Active, (active_edge, type(active_edge))
    i, j, lbl, _, p, rule = active_edge
    newrule = update_rule(rule, lbl, p, found, sequences)
    k = found[-1]
    add_active_edge(i, k, lbl, p+1, newrule, sequences, active_chart, add_edge, name)
    

def add_active_edge(i, k, lbl, p, rule, sequences, active_chart, add_edge, name):
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
    add_edge(newedge, active_chart[k][nextsym], name)


def update_rule(rule, lbl, p, newarg, sequences):
    fun, cat, args = rule
    argnr, _arglbl = sequences[fun][lbl][p]
    newargs = args[:argnr] + (newarg,) + args[argnr+1:]
    return Rule(fun, cat, newargs)



######################################################################
## helper classes and functions

Symbol = namedtuple("Symbol", "cat lbl")

RHSSymbol = namedtuple("RHSSymbol", "arg lbl")
RHSSymbol.toSymbol = lambda self, args: Symbol(args[self[0]], self[1])

Found = namedtuple("Found", "cat lbl start end")

Active = namedtuple("Active", "start end lbl nextsym pos rule")

# Predict = namedtuple("Predict", "cat lbl")

Rule = namedtuple("Rule", "fun cat args")


######################################################################
## pretty-printing 

def print_chart(chart, tokens, startcats, sequences):
    for k in range(1 + len(tokens)):
        print_chartstate(k, chart, tokens, sequences)
    print_dynrules(chart)
    print_startcats(startcats)


def print_startcats(startcats):
    print "# Starting categories:",
    print ", ".join(map(str, startcats))
    print


def print_dynrules(chart):
    print "# Dynamic rules"
    for cat in sorted(chart[Rule]):
        for rule in sorted(chart[Rule][cat]):
            fun, _cat, args = rule
            assert _cat == cat, "CAT MISMATCH: %s == %s / %s" % (show_cat(_cat), show_cat(cat), show_rule(rule))
            print show_rule(rule)
    print


def print_chartstate(k, chart, tokens, sequences):
    print "# %s: %s" % (k, tokens[k-1] if k > 0 else "--START--")
    print "PREDICT:", ", ".join(show_predict_edge(e) for e in sorted(chart[Symbol][k]))
    found = set.union(*chart[Found][k].values())
    print "FOUND:", ", ".join(show_found_edge(e) for e in sorted(found))
    for edge in sorted(set.union(*chart[Active][k].values())):
        print show_active_edge(edge, sequences)
    print


def trace_edge(name, edge, sequences):
    print "%-10s|" % (name,),
    if type(edge) is Active:
        print "   " + show_active_edge(edge, sequences)
    elif type(edge) is Symbol:
        print "?  " + show_predict_edge(edge)
    elif type(edge) is Found:
        print "+  " + show_found_edge(edge)
    elif type(edge) is Rule:
        print "-> " + show_rule(edge)


def show_predict_edge(edge):
    cat, lbl = edge
    return "?%s.%s" % (show_cat(cat), show_lbl(lbl))


def show_found_edge(cat):
    return show_cat(cat)


def show_active_edge(edge, sequences):
    i, k, lbl, nextsym, p, rule = edge
    fun, _cat, _args = rule
    rhs = sequences[fun][lbl]
    return ("%s-%s. %s = %s | %s" % (i, k, show_lbl(lbl), show_rhs(rhs, p), show_rule(rule)))


def show_lbl(lbl):
    if isinstance(lbl, int):
        return "s%s" % lbl
    else:
        return "%s" % lbl


def show_cat(cat):
    if type(cat) is Found:
        cat0, lbl, j, k = cat
        return "%s:%s=%s-%s" % (show_cat(cat0), show_lbl(lbl), j, k)
    else:
        return "%s" % (cat,)


def show_sym(sym):
    if isinstance(sym, tuple):
        return "<%s.%s>" % (sym[0], show_lbl(sym[1]))
    else:
        return "%s" % sym


def show_rhs(rhs, p=None):
    if p is None:
        return " ".join(map(show_sym, rhs))
    else:
        return "%s * %s" % (show_rhs(rhs[:p]), show_rhs(rhs[p:]))


def show_rule(rule):
    try:
        fun, cat, args = rule
        rhs_suffix = ""
    except ValueError:
        fun, cat, args, rhss = rule
        rhs_suffix = " = " + ", ".join("%s: [%s]" % (show_lbl(lbl), " ".join(map(show_sym, rhs))) 
                                       for lbl, rhs in rhss.iteritems())
    return "%s. %s <- (%s)%s" % (showfun(fun), show_cat(cat), ", ".join(map(show_cat, args)), rhs_suffix)


def showfun(fun):
    # if type(fun) is tuple:
    #     return "(%s)" % "/".join(map(showfun, fun))
    # else:
    return "%s" % (fun,)

