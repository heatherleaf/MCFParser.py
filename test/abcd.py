
grammar = [
    # S -> f(A) = {s0 = A.s0 A.s1}
    ('f', 'S', ('A',), {'s': [(0, 'p'), (0, 'q')]}),

    # A -> g(A) = {s0 = "a" A.s0 "b"; s1 = "c" A.s1 "d"}
    ('g', 'A', ('A',), {'p': ['a', (0, 'p'), 'b'], 'q': ['c', (0, 'q'), 'd']}),

    # A -> h() = {s0 = "a" "b"; s1 = "c" "d"}
    ('h', 'A', (), {'p': ['a', 'b'], 'q': ['c', 'd']}),
]

sentences = [
    (1, list("a"*n + "b"*n + "c"*n + "d"*n))
    for n in range(1, 5)
]

