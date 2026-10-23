"""Exact finite audit checks. These do not prove unbounded Lean statements."""
from itertools import product, combinations_with_replacement
from json import dumps

summary = {}
relations = partial_injections = 0
for n, m in product(range(4), repeat=2):
    for bits in product((False, True), repeat=n*m):
        r = {(a,b) for a in range(n) for b in range(m) if bits[a*m+b]}
        rows = [{b for aa,b in r if aa == a} for a in range(n)]
        cols = [{a for a,bb in r if bb == b} for b in range(m)]
        right = all(len(row) <= 1 for row in rows)
        left = all(len(col) <= 1 for col in cols)
        selected = [min(row) if row else None for row in rows]
        inverse = [min(col) if col else None for col in cols]
        if right:
            assert {(a,b) for a,b in enumerate(selected) if b is not None} == r
        if left and right:
            assert all((selected[a] == b) == (inverse[b] == a)
                       for a in range(n) for b in range(m))
            assert all((sum(aa == a for aa,_ in r) == 0) == (selected[a] is None)
                       for a in range(n))
            assert all((sum(bb == b for _,bb in r) == 0) == (inverse[b] is None)
                       for b in range(m))
            partial_injections += 1
        relations += 1
summary['relations_dimensions_0_through_3'] = relations
summary['partial_injections'] = partial_injections

# Every inflationary map on the full Boolean lattices on n <= 3 elements.
inflationary = 0
for n in range(4):
    size = 1 << n
    choices = [[b for b in range(size) if a & b == a] for a in range(size)]
    for f in product(*choices):
        a = 0
        for _ in range(n):
            if f[a] != a:
                assert bin(a).count('1') < bin(f[a]).count('1')
            a = f[a]
        assert f[a] == a
        inflationary += 1
summary['inflationary_boolean_maps_n_le_3'] = inflationary

# All monotone maps of finite total orders of size at most six.
monotone = 0
for n in range(1, 7):
    for f in combinations_with_replacement(range(n), n):
        fixed = [a for a in range(n) if f[a] == a]
        assert fixed
        top, bot = n-1, 0
        for _ in range(n):
            top, bot = f[top], f[bot]
        assert top == max(fixed)
        assert bot == min(fixed)
        monotone += 1
summary['monotone_chain_maps_card_le_6'] = monotone

# Guard against incorrectly dropping the explicit closure hypotheses in
# FixedPointLattice: this is a counterexample to that stronger statement.
f = lambda a: (a | 4) if a & 3 == 3 else a
assert all(not (a & b == a) or (f(a) & f(b) == f(a))
           for a,b in product(range(8),repeat=2))
assert f(1) == 1 and f(2) == 2 and f(1 | 2) == 7 != 3
summary['fixed_points_need_not_close_under_ambient_join'] = {
    'carrier': 'P({0,1,2}), subsets encoded as bit masks',
    'map': [f(a) for a in range(8)],
    'fixed_p': 1, 'fixed_q': 2, 'ambient_join': 3,
    'image_of_ambient_join': 7,
}
print(dumps(summary, indent=2, sort_keys=True))
