#!/usr/bin/env python3
"""Bounded sanity checks, not proofs of general selection theorems.

The singleton star-refinement check is a counterexample to the stronger
interpretation that the output conjunction guarantees every indexed set nonempty;
this is only a documentation/API-strength observation, not a false theorem.
The other checks stress direct interpretations of audited definitions.
All calculations are exact, using finite sets, integers and rational numbers.
"""
from fractions import Fraction
from itertools import product
import json

# Exact explicit countermodel to the claimed *all members nonempty* output property.
# In the discrete singleton topology all subsets are open; every finite indexed
# family is locally finite. π is the unique map Bool -> PUnit.
X = frozenset({0})
C = {0: X}
S = {False: X, True: frozenset()}
pi = {False: 0, True: 0}
assert frozenset().union(*S.values()) == X
assert all(s <= C[pi[k]] for k, s in S.items())
assert all(not (s1 & s2) or s1 <= C[pi[k2]]
           for k1, s1 in S.items() for k2, s2 in S.items())
assert not all(bool(s) for s in S.values())

# For every finite nonempty real set a in this grid, the strict infimum-distance
# characterization equals Minkowski addition with the open epsilon ball.
Y = tuple(map(Fraction, range(-2, 3)))
metric_checks = 0
for bits in product((False, True), repeat=len(Y)):
    a = tuple(y for y, chosen in zip(Y, bits) if chosen)
    if not a:
        continue  # Imported infDist convention at ∅ is deliberately not tested.
    for f, eps in product(Y, (Fraction(-1), Fraction(0), Fraction(1, 2), Fraction(1), Fraction(2))):
        minkowski_ball = any(abs(f - y) < eps for y in a)
        inf_dist = min(abs(f - y) for y in a) < eps
        assert minkowski_ball == inf_dist
        metric_checks += 1

# Closed finite subsets of Baire space represented by two coordinates then zero
# forever. Greedy least admissible prefixes must equal the true lexicographic min.
branches = tuple(product(range(3), repeat=2))
prefix_checks = 0
for bits in product((False, True), repeat=len(branches)):
    K = tuple(b for b, chosen in zip(branches, bits) if chosen)
    if not K:
        continue
    prefix = ()
    for n in range(5):
        if n < 2:
            choices = [b[n] for b in K if b[:n] == prefix]
        else:
            choices = [0]
        prefix += (min(choices),)
        assert prefix == (min(K) + (0, 0, 0))[:n + 1]
        prefix_checks += 1
print(json.dumps({
    'singleton_star_refinement_formal_conclusion': True,
    'singleton_star_refinement_all_nonempty': False,
    'metric_grid_equivalence_checks': metric_checks,
    'closed_finite_baire_prefix_checks': prefix_checks,
    'scope': 'Exact finite witnesses/checks only; no general theorem inferred.'
}, indent=2))
