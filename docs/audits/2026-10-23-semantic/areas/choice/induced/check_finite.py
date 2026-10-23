"""Exact finite checks of the audited choice-constructor semantics.

All sets are bitmasks, all rankings are explicit permutations worst-to-best.
This checks the bounded encodings stated below, not arbitrary-domain theorems.
"""
from itertools import combinations, permutations, product

N = 3
MENUS = tuple(range(1 << N))

def subset(x, y):
    return x & ~y == 0

def submenus(y):
    return tuple(x for x in MENUS if subset(x, y))

def irc(choice, menus):
    return all(choice[z] == choice[y]
               for y in menus for z in menus
               if subset(choice[y], z) and subset(z, y))

def substitutes(choice, menus):
    return all(subset(choice[y] & z, choice[z])
               for y in menus for z in menus if subset(z, y))

def unit(choice):
    return all(bin(x).count("1") <= 1 for x in choice)

def lad(choice, menus):
    return all(bin(choice[y]).count("1") <= bin(choice[z]).count("1")
               for y in menus for z in menus if subset(y, z))

bundle_orders = 0
bundle_menu_cases = 0
for k in range(len(MENUS) + 1):
    for family in combinations(MENUS, k):
        for order in permutations(family):
            rank = {bundle: i for i, bundle in enumerate(order)}
            choice = []
            for y in MENUS:
                feasible = tuple(b for b in family if subset(b, y))
                # Membership definition: union of all greatest feasible bundles.
                witnesses = tuple(b for b in feasible
                                  if all(rank[c] <= rank[b] for c in feasible))
                formal = 0
                for b in witnesses:
                    formal |= b
                # Independently expressed intended finite selection specification.
                intended = max(feasible, key=rank.__getitem__) if feasible else 0
                assert formal == intended
                assert len(witnesses) <= 1
                choice.append(formal)
                bundle_menu_cases += 1
            assert irc(choice, MENUS)
            bundle_orders += 1

option_cases = 0
for order in permutations(range(N + 1)):
    # 0 is none, i+1 is some i.
    rank = {option: i for i, option in enumerate(order)}
    choice = []
    for y in MENUS:
        options = (0,) + tuple(i + 1 for i in range(N) if y & (1 << i))
        best = max(options, key=rank.__getitem__)
        intended = 0 if best == 0 else 1 << (best - 1)
        formal = sum(1 << i for i in range(N)
                     if y & (1 << i)
                     and rank[0] <= rank[i + 1]
                     and all(rank[j + 1] <= rank[i + 1]
                             for j in range(N) if y & (1 << j)))
        assert formal == intended
        choice.append(formal)
        option_cases += 1
    assert unit(choice) and irc(choice, MENUS)
    assert substitutes(choice, MENUS) and lad(choice, MENUS)

# All 4096 contracting choice functions on a 3-alternative domain,
# pushed along e(0)=0,e(1)=2,e(2)=3 into a 4-alternative domain.
EMBED = (0, 2, 3)
LARGE_MENUS = tuple(range(1 << 4))

def image(x):
    return sum(1 << EMBED[i] for i in range(N) if x & (1 << i))

def preimage(y):
    return sum(1 << i for i in range(N) if y & (1 << EMBED[i]))

mapped_seen = set()
map_cases = 0
for original in product(*(submenus(y) for y in MENUS)):
    mapped = tuple(image(original[preimage(y)]) for y in LARGE_MENUS)
    assert all(subset(mapped[y], y) for y in LARGE_MENUS)
    assert all(mapped[image(y)] == image(original[y]) for y in MENUS)
    assert all(not (v & (1 << 1)) for v in mapped)  # outside range ignored
    assert not unit(original) or unit(mapped)
    assert not irc(original, MENUS) or irc(mapped, LARGE_MENUS)
    assert not substitutes(original, MENUS) or substitutes(mapped, LARGE_MENUS)
    assert not lad(original, MENUS) or lad(mapped, LARGE_MENUS)
    mapped_seen.add(mapped)
    map_cases += 1
assert len(mapped_seen) == map_cases

print(f"PASS: {bundle_orders} ranked represented families, "
      f"{bundle_menu_cases} bundle/menu cases; "
      f"{option_cases} option-order/menu cases; "
      f"{map_cases} arbitrary contracting maps, injection and property preservation.")
