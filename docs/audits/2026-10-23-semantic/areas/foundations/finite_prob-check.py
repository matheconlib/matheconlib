"""Exact bounded corroboration of the finite-probability semantic audit.

The event, joint, and binary-product loops were independently authored and run
by the hostile reviewer, then retained here verbatim apart from formatting.
The final basic/expectation loops were authored by the area auditor.
This is a faithful translation of displayed finite formulas, not a Lean build
or a proof of unrestricted equivalence.
"""

from fractions import Fraction as Q
from itertools import product

checked = 0
for n in range(1, 5):
    for nums in product(range(5), repeat=n):
        if sum(nums) != 4:
            continue
        p = tuple(Q(k, 4) for k in nums)
        for bits in product((False, True), repeat=n):
            e = sum((p[i] for i in range(n) if bits[i]), Q(0))
            cp = tuple(p[i] / e if bits[i] and e > 0 else Q(0) for i in range(n))
            assert sum(cp) == (1 if e > 0 else 0)
            assert all(e * cp[i] == (p[i] if bits[i] else 0) for i in range(n))
            total = cp if e > 0 else p
            assert sum(total) == 1
            for other in product((False, True), repeat=n):
                if e:
                    lhs = sum((total[i] for i in range(n) if other[i]), Q(0))
                    rhs = sum((p[i] for i in range(n) if other[i] and bits[i]), Q(0)) / e
                    assert lhs == rhs
            checked += 1

joint_checks = 0
for nums in product(range(5), repeat=4):
    if sum(nums) != 4:
        continue
    p = {xy: Q(k, 4) for xy, k in zip(product(range(2), repeat=2), nums)}
    for i in range(2):
        marg = [sum((p[x] for x in p if x[i] == b), Q(0)) for b in range(2)]
        assert sum(marg) == 1
        for b in range(2):
            cp = {x: (p[x] / marg[b] if x[i] == b and marg[b] > 0 else Q(0)) for x in p}
            assert sum(cp.values()) == (1 if marg[b] > 0 else 0)
            assert all(marg[b] * cp[x] == (p[x] if x[i] == b else 0) for x in p)
            joint_checks += 1

for a, b in product(range(5), repeat=2):
    p = (Q(a, 4), 1 - Q(a, 4))
    q = (Q(b, 4), 1 - Q(b, 4))
    law = {(i, j): p[i] * q[j] for i, j in product(range(2), repeat=2)}
    assert sum(law.values()) == 1
    assert all(sum(law[i, j] for j in range(2)) == p[i] for i in range(2))
    assert all(sum(law[i, j] for i in range(2)) == q[j] for j in range(2))
print(f"PASS: {checked} event cases; {joint_checks} binary joint-coordinate cases; "
      "25 binary product laws. Exact Fraction arithmetic, bounded verification only.")


def laws(n):
    return [tuple(Q(k, 4) for k in nums)
            for nums in product(range(5), repeat=n) if sum(nums) == 4]


def expectation(p, f):
    return sum((w * value for w, value in zip(p, f)), Q(0))


basic_cases = expectation_cases = mixture_cases = 0
assert laws(0) == []  # No probability distribution on the empty outcome set.
empty_profile_law = {(): Q(1)}  # Empty product has exactly one empty profile.
assert sum(empty_profile_law.values()) == 1
for n in range(1, 5):
    ds = laws(n)
    uniform = tuple(Q(1, n) for _ in range(n))
    assert sum(uniform) == 1
    assert all(x == max(uniform) for x in uniform)
    for p in ds:
        assert all(0 <= w <= 1 for w in p) and sum(p) == 1
        support = {i for i, w in enumerate(p) if w > 0}
        modes = {i for i, w in enumerate(p) if all(v <= w for v in p)}
        assert support and modes <= support
        if len(support) == 1:
            (a,) = support
            assert p[a] == 1
        for f in product((-1, 0, 1), repeat=n):
            ef = expectation(p, f)
            assert min(f) <= ef <= max(f)
            support_max = all(f[a] == max(f) for a in support)
            assert support_max == (ef == max(f))
            if all(value <= ef for value in f):
                assert all(f[a] == ef for a in support)
            expectation_cases += 1
        basic_cases += 1
    for p, q in product(ds, repeat=2):
        for k in range(5):
            t = Q(k, 4)
            mix = tuple(t * x + (1 - t) * y for x, y in zip(p, q))
            assert sum(mix) == 1 and all(w >= 0 for w in mix)
            if 0 < t < 1:
                assert {i for i, w in enumerate(mix) if w > 0} == {
                    i for i in range(n) if p[i] > 0 or q[i] > 0}
            f = tuple(range(n))
            assert expectation(mix, f) == t * expectation(p, f) + (1 - t) * expectation(q, f)
            mixture_cases += 1
print(f"PASS: {basic_cases} probability vectors; {expectation_cases} expectation cases; "
      f"{mixture_cases} mixture cases; empty carrier and empty profile edge cases.")
