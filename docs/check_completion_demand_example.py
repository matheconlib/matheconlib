"""Auxiliary exhaustive check; not a substitute for Lean verification.

Bits 0,1,2,3 represent a,a',b,c; counterparties are 0,0,1,2.
"""
from itertools import product

MENUS = range(16)
PARTNER = (0, 0, 1, 2)
RANKING = (12, 4, 10, 8, 1, 2, 0)


def subset(a, b):
    return a & b == a


def feasible(menu):
    partners = [PARTNER[i] for i in range(4) if menu & (1 << i)]
    return len(partners) == len(set(partners))


def allowed(menu, choice):
    return subset(choice, menu) and (choice == C[menu] or not feasible(choice))


C = [next(bundle for bundle in RANKING if subset(bundle, menu)) for menu in MENUS]
assert all(feasible(C[y]) for y in MENUS)
assert all(C[v] == C[y] for v, y in product(MENUS, repeat=2)
           if subset(C[y], v) and subset(v, y))
assert all(C[v].bit_count() <= C[y].bit_count()
           for v, y in product(MENUS, repeat=2) if subset(v, y))
for y, x, z in product(MENUS, range(4), range(4)):
    if any(y & (1 << i) and PARTNER[i] == PARTNER[x] for i in range(4)):
        continue
    if not C[y | (1 << x)] & (1 << x):
        assert not C[y | (1 << x) | (1 << z)] & (1 << x)

# All completions on {a,a',c} choose a'; substitution forces it on {a,a'}.
assert all(choice & 2 for choice in MENUS if allowed(11, choice))
assert [choice for choice in MENUS if allowed(3, choice) and choice & 2] == [3]
# Feasible sub-menus exclude a and a' on {a,a',b}.
assert C[5] == C[6] == 4
assert [choice for choice in MENUS if allowed(7, choice) and not choice & 3] == [4]
assert (3).bit_count() > (4).bit_count()
print('Verified IRC, feasibility, unilateral substitutability, demand monotonicity,')
print('and the forced demand violation for every substitutable completion.')
