"""Independent finite semantics check for Choice/Matching (three contracts).

Bit i represents contract i. A choice table C assigns each menu a submask.
This checks the exact finite encoding, not an unrestricted theorem.
"""
from itertools import product
import json

n = 3
menus = range(1 << n)
submasks = {s: [t for t in menus if t & ~s == 0] for s in menus}
pairs = [(s, t) for s in menus for t in menus if s & ~t == 0]
partitions = [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (0, 1, 2)]

def irc(c):
    return all(c[t] == c[s] for s in menus for t in submasks[s]
               if c[s] & ~t == 0)

def sub(c):
    return all(c[t] & s & ~c[s] == 0 for s, t in pairs)

def hull(c):
    return tuple(s & union(c[t] for t in menus if s & ~t == 0) for s in menus)

def union(xs):
    result = 0
    for x in xs:
        result |= x
    return result

def fresh(p, x, s):
    return all(not s & (1 << y) or p[y] != p[x] for y in range(n))

def us(c, p, bilateral=False):
    return all(not (fresh(p, x, s)
                    and (not bilateral or fresh(p, z, s))
                    and not c[s | (1 << x)] & (1 << x))
               or not c[s | (1 << x) | (1 << z)] & (1 << x)
               for x in range(n) for z in range(n) for s in menus)

def feasible(s, p):
    return all(not (s & (1 << x) and s & (1 << y)) or p[x] != p[y]
               for x in range(n) for y in range(x))

def completion(c, d, p):
    return all(c[s] == d[s] or not feasible(d[s], p) for s in menus)

def image(s, p):
    return {p[x] for x in range(n) if s & (1 << x)}

counts = {str(p): {"choice_tables": 0, "US_IRC_feasible": 0} for p in partitions}
for c in product(*(submasks[s] for s in menus)):
    h = hull(c)
    # Check the closure independently of any partner data.
    assert sub(h)
    assert all(c[s] & ~h[s] == 0 for s in menus)
    if irc(c):
        assert irc(h)
    for p in partitions:
        count = counts[str(p)]
        count["choice_tables"] += 1
        unilateral = us(c, p)
        bilateral = us(c, p, bilateral=True)
        assert not unilateral or bilateral
        img_equal = all(image(h[s], p) == image(c[s], p) for s in menus)
        # Unconditional implication from hull image preservation.
        assert not img_equal or unilateral
        if irc(c) and all(feasible(c[s], p) for s in menus):
            assert unilateral == img_equal
            assert unilateral == completion(c, h, p)
            if unilateral:
                count["US_IRC_feasible"] += 1
                assert sub(h) and irc(h)

print(json.dumps(counts, indent=2))
