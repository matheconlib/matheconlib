"""Exact bounded checks of the mathematical translations in Schauder.lean.
This is independent Python evidence, not a Lean compile check or a general proof.
Orders are enumerated as permutations ranked from least to greatest. Fractions
are represented by integer numerators on a fixed positive grid denominator.
Run: python3 docs/audits/2026-10-23-semantic/areas/foundations/selection-schauder-check.py
"""
from itertools import permutations, product
from collections import Counter
import json


def subsets(m):
    return [frozenset(i for i in range(m) if mask & (1 << i)) for mask in range(1 << m)]


def raw_dominant(ranks, sigma, C, m):
    # Literal translation of line 58 (not involving minima).
    return all(any(all(not (ranks[i][x] < ranks[i][y]) for x in sigma)
                   for i in C) for y in range(m))


def standard_dominant(ranks, sigma, C, m):
    # Standard convention: empty sigma dominant for nonempty C.
    if not C:
        return m == 0   # extension outside the standard C-nonempty domain
    if not sigma:
        return True
    mins = {i: min(sigma, key=lambda x: ranks[i][x]) for i in C}
    return not any(all(ranks[i][mins[i]] < ranks[i][y] for i in C) for y in range(m))


def adjacent(v, w):
    # Literal structural relation of lines 64-70.
    def directed(a, b):
        s, C = a
        return (len(s) == len(C) and
                (any(b == (s - {x}, C) for x in s) or
                 any(b == (s, C | {i}) for i in range(q) if i not in C)))
    return v != w and (directed(v, w) or directed(w, v))


counts = Counter()
for m in range(1, 4):
    S = subsets(m)
    orderings = list(permutations(range(m)))
    ranks_all = [tuple(p.index(x) for x in range(m)) for p in orderings]
    for q in range(1, 4):
        colorsets = subsets(q)
        for ranks in product(ranks_all, repeat=q):
            dom = {(s, C): raw_dominant(ranks, s, C, m) for s in S for C in colorsets}
            for s in S:
                for C in colorsets:
                    assert dom[s, C] == standard_dominant(ranks, s, C, m)
                    counts['dominance_equivalences'] += 1
                    if dom[s, C]:
                        assert len(s) <= len(C)
                        if s:
                            assert {min(s, key=lambda x: ranks[i][x]) for i in C} == s
                            counts['minimum_surjections'] += 1
            for c in product(range(q), repeat=m):
                image = {s: frozenset(c[x] for x in s) for s in S}
                colorful = [(s, C) for s in S for C in colorsets
                            if C and dom[s, C] and C == image[s]]
                assert colorful
                assert all(len(s) == len(C) and s for s, C in colorful)
                counts['colorful_room_existence'] += 1
                for i0 in range(q):
                    V = [(s, C) for s in S for C in colorsets if C and dom[s, C] and
                         ((len(s) == len(C) and C == image[s]) or
                          (len(s) == len(C) and C - image[s] == {i0}) or
                          (len(C) == len(s) + 1 and C - image[s] == {i0}))]
                    for v in V:
                        s, C = v
                        degree = sum(adjacent(v, w) for w in V)
                        expected = 1 if (v in colorful or not s) else 2
                        assert degree == expected
                        if len(C) == len(s) + 1:
                            assert image[s] <= C
                            assert len(image[s]) == len(s)  # coloring injective on a door
                        counts['vertex_degrees'] += 1
                    assert (frozenset(), frozenset({i0})) in V
                    counts['scarf_graphs'] += 1


def compositions(total, parts):
    if parts == 1:
        yield (total,)
    else:
        for j in range(total + 1):
            for rest in compositions(total-j, parts-1):
                yield (j,) + rest

# Exact geometric form: coordinate minima and sums are integer numerator values.
for q in range(1, 4):
    for l in range(1, 5):
        grid = list(compositions(l, q))
        # Rotation is a permutation and makes the designated coordinate first.
        for i in range(q):
            rotated = [tuple(x[(i+j) % q] for j in range(q)) for x in grid]
            assert len(set(rotated)) == len(grid)
            for a, x in enumerate(grid):
                for b, y in enumerate(grid):
                    if x[i] < y[i]:
                        assert rotated[a] < rotated[b]
                        counts['coordinate_lex_compatibilities'] += 1
        # All nonempty sigma (<=15 grid points), all C, integer exact dominance.
        for s in subsets(len(grid))[1:]:
            mins = tuple(min(grid[x][i] for x in s) for i in range(q))
            for C in subsets(q):
                dominant = not any(all(mins[i] < y[i] for i in C) for y in grid)
                if not dominant:
                    continue
                assert l - sum(mins[i] for i in C) < len(C)  # key_ineq
                for x in s:
                    for i in range(q):
                        base = mins[i] if i in C else 0
                        assert grid[x][i] - base < q
                        if i not in C:
                            assert grid[x][i] < q
                        for y in s:
                            assert abs(grid[x][i] - grid[y][i]) < 2*q
                counts['coordinate_dominant_rooms_checked'] += 1
print(json.dumps({'status': 'PASS', 'checks': dict(counts),
                  'scope': 'all orders and colorings for |T|=1..3, |I|=1..3; '
                           'simplex grid dimensions 0..2, denominators 1..4',
                  'limitation': 'bounded exact Python evidence, no general theorem or Lean compile claim'},
                 indent=2, sort_keys=True))
