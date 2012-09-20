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

import itertools
from collections import namedtuple

import MCFParser

META = "{?}"


class PGF(object):
    def __init__(self, data):
        self._data = data
        self.flags = data['flags']
        self.abstract = Abstract(data['abstract'])
        self.concretes = dict((lang, Concrete(lang, cnc, self.abstract)) 
                              for (lang, cnc) in data['concretes'].items())

    def typecheck(self, tree, typ):
        return self.abstract.typecheck(tree, typ)

    def __getitem__(self, lang):
        return self.concretes[lang]

    def __str__(self):
        return unicode(self).encode('utf-8')

    def __unicode__(self):
        return (unicode(self.abstract) + "\n" + 
                "\n".join(unicode(cnc) for cnc in self.concretes.values()))


class Abstract(object):
    def __init__(self, data):
        self._data = data
        self.name = data['name']
        self.start = data['start']
        self.flags = data['flags']
        self.funs = data['funs']

    def typecheck(self, tree, typ):
        """Checks that a tree is type correct. Returns silently or raises a TypeError."""
        if tree is None:
            return
        if not isinstance(tree, (list, tuple)):
            raise ValueError("Tree not a list or tuple: %s" % tree)
        ftyp, childtypes = self.funs[tree[0]]
        if typ != ftyp:
            raise TypeError("Type mismatch, %s != %s" % (typ, ftyp))
        for child, childtype in zip(tree[1:], childtypes):
            self.typecheck(child, childtype)

    def __str__(self):
        return unicode(self).encode('utf-8')

    def __unicode__(self):
        return ("-- ABSTRACT: %s\n\n" % self.name + 
                "startcat %s\n\n" % self.start +
                "".join("fun %s : (%s) -> %s\n" % (fun, ",".join(args), res)
                        for (fun, (res, args)) in self.funs.items()))


class Concrete(object):
    def __init__(self, lang, data, abstract):
        self._data = data
        self.abstract = abstract
        self.lang = lang
        self.flags = data['flags']
        self.printnames = data['printnames']
        self.lindefs = data['lindefs']
        self.productions = data['productions']
        self.cncfuns = data['cncfuns']
        self.sequences = data['sequences']
        self.cnccats = data['cnccats']
        self.nr_cats = data['size']

        self.parsers = {}

        self.linfuns = {}
        self.coercions = {}
        self.arities = {}
        for cat, prods in self.productions.iteritems():
            self.coercions.setdefault(cat, []).append(cat)
            for fname, args in prods:
                if not fname:
                    assert len(args) == 1, ("Error in coercion, there are %d args "
                                            "for coercion of category %s" % (len(args), cat))
                    self.coercions.setdefault(args[0], []).append(cat)
                else:
                    seqs, fun = self.cncfuns[fname]
                    self.linfuns.setdefault(fun, {}).setdefault(tuple(args), []).append((fname, cat, seqs))
                    arity = len(seqs)
                    if cat in self.arities:
                        assert arity == self.arities[cat], ("Mismatching linfun arities for cat: %s (%d==%d)" 
                                                            % (cat, arity, self.arities[cat]))
                    else:
                        self.arities[cat] = arity
        self.max_arity = max(self.arities.values())

    ######################################################################

    def __str__(self):
        return unicode(self).encode('utf-8')

    def __unicode__(self):
        s = ["## CONCRETE: %s" % self.lang, ""]

        s += ["# coercions"]
        s += ["%s -> %s" % (cat, " | ".join(cats))
              for cat, cats in sorted(self.coercions.items())]
        s += [""]

        s += ["# linfuns = productions + cncfuns"]
        s += ["%s. %s : (%s) -> %s  ...  [%s]" %
              (fun, fname, ",".join(children), cat, "+".join(seqs))
              for fun, linfun in sorted(self.linfuns.items())
              for children, alts in sorted(linfun.items())
              for (fname, cat, seqs) in alts]
        s += [""]

        s += ["# sequences"]
        s += ["%s = " % snr +
              " ".join(("<%d.%d>" % arg if isinstance(arg, tuple) 
                        else "%s" % arg) for arg in seq)
              for (snr, seq) in self.sequences.items()]
        s += [""]
        # if isinstance(arg, tuple):
        #     print "<%d.%d>" % arg,
        # elif isinstance(arg, dict):
        #     print arg,
        # else:
        #     print " ".join(arg),

        s += ["# cnccats"]
        s += ["%s :-> %s" % (cat, " ; ".join(ccats))
              for cat, ccats in sorted(self.cnccats.items())]
        s += [""]

        s += ["# nr cats: %d" % self.nr_cats]
        return u"\n".join(s) + "\n"

    ######################################################################

    def linearise(self, tree):
        """returns a (str,path) list"""
        for _cat, lin in self._linearise_nondet(tree):
            return self._expand_tokens(lin[0])

    def linearise_all(self, tree):
        """returns a tuple of (str,path) lists"""
        for _cat, lin in self._linearise_nondet(tree):
            return self._expand_tokens(lin)

    def linearise_nondet(self, tree):
        """returns a generator of a tuple of (str,path) lists"""
        for _cat, lin in self._linearise_nondet(tree):
            yield self._expand_tokens(lin)

    def _expand_tokens(self, lin):
        if not lin:
            return lin
        elif isinstance(lin, list) and isinstance(lin[0], tuple):
            newlin = []
            for tokens, alternatives, path in reversed(lin):
                if newlin:
                    for alttokens, prefixes in alternatives:
                        if any(newlin[0][0].startswith(pre) for pre in prefixes):
                            tokens = alttokens
                            break
                newlin[:0] = zip(tokens, itertools.repeat(path))
            return newlin
        elif isinstance(lin, tuple) and isinstance(lin[0], list):
            return tuple(self._expand_tokens(phrase) for phrase in lin)
        else:
            raise ValueError("Unknown linearisation: %s" % lin)

    def _linearise_nondet(self, tree, path=()):
        linfuns = self.linfuns[tree[0]]
        for children_cats, children_lins in self._linearise_children_nondet(tree, path):
            for (fun, cat, seqs) in linfuns.get(children_cats, ()):
                lin = tuple([] for _ in seqs)
                for i, seqnr in enumerate(seqs):
                    seq = self.sequences[seqnr]
                    phrase = lin[i]
                    for arg in seq:
                        if isinstance(arg, tuple):
                            phrase += children_lins[arg[0]][arg[1]]
                        elif isinstance(arg, basestring):
                            phrase.append(([arg], [], path))
                        elif isinstance(arg, list):
                            phrase.append((arg, [], path))
                        elif 'pre' in arg:
                            phrase.append((arg['pre'], arg['alts'], path))
                        else:
                            raise ValueError("Unrecognised sequence item: %r" % arg)
                yield cat, lin

    def _linearise_children_nondet(self, tree, path):
        if len(tree) > 1:
            all_catlins = [list(self._linearise_child_nondet(tree[0], arg, path, i))
                           for i, arg in enumerate(tree) if i > 0]
            for catlins in itertools.product(*all_catlins):
                cats, lins = zip(*catlins)
                coerced = [self.coercions[cat] for cat in cats]
                for cocats in itertools.product(*coerced):
                    yield cocats, lins
        else:
            yield (), ()

    def _linearise_child_nondet(self, parent, child, path, i):
        if child is None:
            _type, argtypes = self.abstract.funs[parent]
            childtype = argtypes[i-1]
            for cat in self.cnccats[childtype]:
                if cat in self.arities:
                    yield cat, tuple([([META], [], path)] for _ in xrange(self.arities[cat]))
        else:
            for result in self._linearise_nondet(child, append_path(path, i)):
                yield result

    ######################################################################

    def parser(self, trace=None, **strategy):
        strategy_key = tuple(sorted(strategy.items()))
        if strategy_key not in self.parsers:
            self.parsers[strategy_key] = GFParser(self, trace, **strategy)
        return self.parsers[strategy_key]


######################################################################

class GFParser(object):
    def __init__(self, concrete, trace=None, **strategy):
        self.concrete = concrete
        startcats = concrete.cnccats[concrete.abstract.start]
        self.mcfparser = MCFParser.Parser(self.mcfrule_iter(), startcats, trace, **strategy)

    def mcfrule_iter(self):
        coercion_rhss = [[(0, lbl)] for lbl in range(self.concrete.max_arity)]
        for ccat, prods in self.concrete.productions.iteritems():
            for cfun, args in prods:
                if cfun: 
                    seqs, _ = self.concrete.cncfuns[cfun]
                    rhss = map(self.convert_gfsequence, seqs)
                else:
                    # coercion
                    assert len(args) == 1
                    cfun = Coercion(ccat, args[0])
                    arity = self.concrete.arities[args[0]]
                    rhss = coercion_rhss[:arity]
                if rhss:
                    yield (cfun, ccat, tuple(args), rhss)

    def convert_gfsequence(self, seq):
        def convert_pre(sym):
            if isinstance(sym, dict):
                # TODO: fix this!!
                if 'pre' in sym:
                    assert isinstance(sym['pre'], list)
                    return sym['pre']
                elif 'lit' in sym:
                    return ["[LITERAL]"]
            return [sym]
        return [mcfsym for gfsym in self.concrete.sequences[seq] for mcfsym in convert_pre(gfsym)]

    def parse(self, tokens, n=None, trace=None):
        for mcftree in self.mcfparser.parse(tokens, n=n, trace=trace):
            yield self.convert_mcftree(mcftree)

    def chart_parse(self, tokens, trace=None):
        return self.mcfparser.chart_parse(tokens, trace=trace)

    @property
    def statistics(self):
        return self.mcfparser.statistics

    def extract_trees(self, startcats=None, start=0, end=None, n=None):
        if isinstance(startcats, basestring):
            startcats = [startcats]
        if startcats:
            startcats = [ccat for cat in startcats for ccat in concrete.cnccats[cat]]
        for mcftree in self.mcfparser.extract_trees(startcats, start, end, n):
            yield self.convert_mcftree(mcftree)

    def convert_mcftree(self, mcftree):
        cfun = mcftree[0]
        if type(cfun) is Coercion:
            assert len(mcftree) == 2, "NOT A COERCION: %s" % str_tree(mcftree)
            return self.convert_mcftree(mcftree[1])
        else:
            _, fun = self.concrete.cncfuns[cfun]
            return (fun,) + tuple(self.convert_mcftree(t) for t in mcftree[1:])


Coercion = namedtuple("Coercion", "cat arg")
Coercion.__str__ = lambda self: "%s+%s" % self


def TDParser(concrete, trace=None):
    return concrete.parser(trace, topdown=True, filtered=False, nonempty=False)

def TDParserNonempty(concrete, trace=None):
    return concrete.parser(trace, topdown=True, filtered=False, nonempty=True)

def BUParser(concrete, trace=None):
    return concrete.parser(trace, bottomup=True, filtered=False, nonempty=False)

def BUParserNonempty(concrete, trace=None):
    return concrete.parser(trace, bottomup=True, filtered=False, nonempty=True)

def TDFilterParser(concrete, trace=None):
    return concrete.parser(trace, topdown=True, filtered=True, nonempty=False)

def TDFilterParserNonempty(concrete, trace=None):
    return concrete.parser(trace, topdown=True, filtered=True, nonempty=True)

def BUFilterParser(concrete, trace=None):
    return concrete.parser(trace, bottomup=True, filtered=True, nonempty=False)

def BUFilterParserNonempty(concrete, trace=None):
    return concrete.parser(trace, bottomup=True, filtered=True, nonempty=True)


def testall(concrete, sentence):
    import itertools, time
    if isinstance(sentence, basestring):
        sentence = sentence.split()
    bools = (True, False)
    names = "topdown bottomup filtered incremental".split()
    for strategy_values in itertools.product((True, False), repeat=4):
        strategy = dict(zip(names, strategy_values))
        try:
            P = concrete.parser(**strategy)
        except AssertionError:
            continue
        print "#", ", ".join(n for n, s in strategy.items() if s)
        t0 = time.clock()
        P.chart_parse(sentence)
        t1 = time.clock() - t0
        for t in P.extract_trees(n=10): 
            print " ", str_tree(t)
        print "-> %d edges, %.2f ms" % (P.chart_statistics()['total'], 1000 * t1)
        print 

######################################################################
## a path is a tuple of integers >= 0

def is_path(path):
    return (isinstance(path, tuple) and
            all(isinstance(n, int) and n >= 0 for n in path))

def append_path(path, n):
    return None if path is None else path + (n,)

def prepend_path(n, path):
    return None if path is None else (n,) + path

def str_path(path):
    return "-" if path is None else "".join(map(str, path))

def lookup_path(tree, path):
    for n in path:
        tree = tree[n]
    return tree

######################################################################
## a linearisation is a list of tokens,
## where a token is a pair (str,path) or a str

def str_lin(lin, marked=None):
    if isinstance(lin, (tuple,list)) and all(isinstance(l, list) for l in lin):
        return " ; ".join(str_lin(phrase, marked) for phrase in lin)
    else:
        return " ".join(str_token(token, marked) for token in lin) 

def str_token(token, marked=None):
    if isinstance(token, basestring):
        return token
    else:
        word, path = token
        star = "*" if is_path(marked) and startswith(path, marked) else ""
        return star + word + "/" + str_path(path)

def startswith(sequence, prefix):
    return sequence[:len(prefix)] == prefix

######################################################################
## a tree is a list/tuple with the first element being the node

def is_tree(tree):
    return (isinstance(tree, (tuple,list)) and
            len(tree) >= 1 and
            isinstance(tree[0], basestring) and
            all(is_tree(child) for child in tree[1:]))

def make_tree(fun, children=()):
    return (fun,) + tuple(children)

def str_tree(tree, path=None):
    star = "*" if path == () else ""
    # if isinstance(tree, (tuple, list)):
    if type(tree) in (tuple, list):
        st = lambda n,t: str_tree(t, path[1:]) if (path and path[0] == n) else str_tree(t)
        return star + "(" + " ".join(st(*q) for q in enumerate(tree)) + ")"
    elif tree is None:
        return "%s%s" % (star, META)
    else:
        return "%s%s" % (star, tree)

def tree_replace_child(tree, n, newchild):
    return tree[:n] + type(tree)((newchild,)) + tree[n+1:]

def tree_replace_subtree(tree, path, subtree):
    if not path:
        return subtree
    else:
        newchild = tree_replace_subtree(tree[path[0]], path[1:], subtree)
        return tree_replace_child(tree, path[0], newchild)

######################################################################
## tree unification

class UnificationFailure(Exception):
    """Raised if unification fails"""

def unify(tree1, tree2):
    """
    Unifies two trees and returns the result. The trees are not modified.
    Raises UnificationFailure if the unification fails.
    """
    if tree1 is None:
        return tree2
    elif tree2 is None:
        return tree1
    elif isinstance(tree1, basestring) or isinstance(tree2, basestring):
        if tree1 == tree2:
            return tree1
        else:
            raise UnificationFailure
    elif len(tree1) != len(tree2):
        raise UnificationFailure
    else:
        return type(tree1)(unify(*child12) for child12 in zip(tree1, tree2))

def unify_child(tree, n, newchild):
    """
    Unifies the specified daugther of the tree with a new child.
    Returns the resulting tree, or None if unsuccessful.
    The original trees are not modified.
    """
    child = unify(tree[n], newchild)
    return tree[:n] + type(tree)([child]) + tree[n+1:]


######################################################################
## tree parsing

def parse_tree(string):
    """
    Parse a bracketed tree string and return the resulting GF tree.
    Trees are represented as nested brackettings, such as::
      (S (NP (NNP (John))) (VP (V (runs))))
    """
    tokens = string.replace("(", " ( ").replace(")", " ) ").split()
    if tokens[0] != "(":
        tokens = ["("] + tokens + [")"]
    tokens.reverse()

    # Walk through each token, updating a stack of trees.
    stack = [(None, [])] # list of (node, children) tuples
    while tokens:
        token = tokens.pop()
        if token == "(":
            if len(stack) == 1 and len(stack[0][1]) > 0:
                raise SyntaxError("Expected end-of-string, found '('")
            if not tokens:
                raise SyntaxError("Expected node, found end-of-string")
            node = tokens.pop()
            if node in "()":
                raise SyntaxError("Expected node, found '%s'" % node)
            stack.append((node, []))

        elif token == ")":
            if len(stack) == 1:
                if len(stack[0][1]) == 0:
                    raise SyntaxError("No matching open bracket, found ')'")
                else:
                    raise SyntaxError("Expected end-of-string, found ')'")
            node, children = stack.pop()
            stack[-1][1].append(make_tree(node, children))

        else:
            if len(stack) == 1:
                raise SyntaxError("Expected '(', found '%s'" % token)
            stack[-1][1].append(make_tree(token))

    # check that we got exactly one complete tree.
    if len(stack) > 1:
        raise SyntaxError("Expected close bracket, found end-of-string")
    elif len(stack[0][1]) == 0:
        raise SyntaxError("Expected open bracket, found end-of-string")
    else:
        assert stack[0][0] is None
        assert len(stack[0][1]) == 1

    tree = stack[0][1][0]
    return tree

