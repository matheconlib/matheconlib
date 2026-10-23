#!/usr/bin/env python3
"""Exact exhaustive audit for every subset-valued choice rule on <=3 alternatives.

Bit k denotes alternative k, and the tuple C has entry C[Y] at menu bitmask Y.
All entries are enumerated among subsets of their menu, so all and only choice
rules on the encoded carrier occur. This finite check is evidence, not a proof
for larger or infinite carriers. No third-party dependencies.
"""
from itertools import product
import json


def is_subset(a, b):
    return (a & b) == a


def popcount(s):
    return bin(s).count('1')


def inspect(n):
    menus = range(1 << n)
    options = [[s for s in menus if is_subset(s, y)] for y in menus]
    pairs = [(y, z) for y in menus for z in menus if is_subset(y, z)]
    all_pairs = [(y, z) for y in menus for z in menus]
    counts = dict(rules=0, substitutable=0, consistent=0, size_monotone=0,
                  unit_demand=0, path_independent=0, repairs=0,
                  terminal=0, longest_selected_repair_run=0)

    def hereditary(c):
        return all(is_subset(c[z] & y, c[y]) for y, z in pairs)

    def irc(c):
        return all(c[z] == c[y] for y, z in pairs if is_subset(c[z], y))

    def hull(c):
        return tuple(sum(1 << x for x in range(n)
                         if y & (1 << x) and
                         any(is_subset(y, z) and c[z] & (1 << x) for z in menus))
                     for y in menus)

    def repair(c, y, z):
        d = list(c)
        d[y] |= y & c[z]
        return tuple(d)

    for c in product(*options):
        counts['rules'] += 1
        h = hereditary(c)
        # Independently transliterate the source's insert/rejection definition.
        insert_sub = all(not (not (c[y | 1 << x] & 1 << x)) or
                         not (c[z | 1 << x] & 1 << x)
                         for x in range(n) for y, z in pairs)
        rejected = tuple(y & ~c[y] for y in menus)
        rejection_monotone = all(is_subset(rejected[y], rejected[z]) for y, z in pairs)
        assert h == insert_sub == rejection_monotone
        consistency = irc(c)
        size_monotone = all(popcount(c[y]) <= popcount(c[z]) for y, z in pairs)
        unit_demand = all(popcount(s) <= 1 for s in c)
        source_pi = all(c[y | z] == c[c[y] | z] for y, z in all_pairs)
        symmetric_pi = all(c[y | z] == c[c[y] | c[z]] for y, z in all_pairs)
        assert source_pi == symmetric_pi == (h and consistency)
        assert not (h and size_monotone) or consistency
        assert not (unit_demand and consistency) or (h and size_monotone)
        hc = hull(c)
        assert all(is_subset(c[y], hc[y]) for y in menus)
        assert hereditary(hc)
        assert hull(hc) == hc
        assert (hc == c) == h
        assert not consistency or irc(hc)
        assert not consistency or all(hc[y | z] == hc[hc[y] | z] for y, z in all_pairs)
        strict = 0
        for y, z in pairs:
            d = repair(c, y, z)
            assert all(is_subset(c[w], d[w]) and is_subset(d[w], hc[w]) for w in menus)
            if d != c:
                strict += 1
        assert (strict == 0) == h
        counts['repairs'] += strict
        counts['terminal'] += strict == 0
        # A definite fair strict schedule, selecting the first available repair.
        d, steps = c, 0
        while True:
            updated = next((repair(d, y, z) for y, z in pairs if repair(d, y, z) != d), None)
            if updated is None:
                break
            old_size = sum(popcount(s) for s in d)
            d = updated
            assert sum(popcount(s) for s in d) > old_size
            steps += 1
            assert steps <= n * (1 << max(n - 1, 0))
        assert d == hc
        counts['longest_selected_repair_run'] = max(counts['longest_selected_repair_run'], steps)
        for name, value in [('substitutable', h), ('consistent', consistency),
                            ('size_monotone', size_monotone), ('unit_demand', unit_demand),
                            ('path_independent', source_pi)]:
            counts[name] += value
    return counts


if __name__ == '__main__':
    print(json.dumps({str(n): inspect(n) for n in range(4)}, indent=2, sort_keys=True))
