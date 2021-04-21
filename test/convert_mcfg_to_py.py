
import re
import json
import fileinput

# F --> AO   a   [0,0;1,0]	(* C --> /T,C   T   [0,0;1,0] *)
# A --> AL   H   [0,0;1,0]	(* D,-case --> /N,D,-case   N   [0,0;1,0] *)
# I --> m   [0,2;0,0][0,1]	(* PastPart,-aux;-case --> +v,PastPart,-aux;-case;-v   [0,2;0,0][0,1] *)
# I --> p   [0,1;0,0][0,2]	(* PastPart,-aux;-case --> +v,PastPart,-aux;-v;-case   [0,1;0,0][0,2] *)
# E --> "laugh"	(* /D,V,-v --> "laugh" *)
# E --> "love"	(* /D,V,-v --> "love" *)

_rule_re = re.compile(r'''
^ (\w+) \s+ --> \s+ ([\w\s]+?) \s+ \[ ([][\d,;]+) \]
''', re.VERBOSE)

_lex_re = re.compile(r'''
^ (\w+) \s+ --> \s+ "([^"]*)"
''', re.VERBOSE)

# >>> grammar = [('f', 'S', ['A'], [[(0,0), (0,1)]]),
# ...            ('g', 'A', ['A'], [['a', (0,0), 'b'], ['c', (0,1), 'd']]),
# ...            ('h', 'A', [],    [['a', 'b'], ['c', 'd']])]

# fun, cat, args, rhss = split_mcfrule(mcfrule)

grammar = []
functr = 1
for line in fileinput.input():
    mrule = re.match(_rule_re, line)
    mlex = re.match(_lex_re, line)
    if mrule:
        cat, args, rhss = mrule.groups()
        args = tuple(args.split())
        rhss = [[tuple(int(i) for i in sym.split(',')) for sym in rhs.split(';')] for rhs in rhss.split('][')]
    elif mlex:
        args = ()
        cat, token = mlex.groups()
        if token:
            rhss = [[token]]
        else:
            rhss = [[]]
    else:
        continue
    fun = f"{cat}-{functr:05d}"
    grammar.append((fun, cat, args, rhss))
    functr += 1

print('grammar = [')
for rule in grammar:
    print(f"    {rule},")
print(']')

