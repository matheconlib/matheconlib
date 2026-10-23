"""Exact finite adversarial checks for the pricing audit.

These checks establish only the explicit rational instances enumerated here;
the general semantic assessments are analytic arguments in README.md.
Run with Python's standard library; no dependency installation is needed.
"""
from fractions import Fraction as Q
from itertools import product


def normalized(weights):
    total = sum(weights)
    return [Q(w, total) for w in weights]


support = [Q(-1), Q(0), Q(1), Q(2)]
prices = [Q(x, 2) for x in range(-4, 7)]
atomic_cases = tail_cases = 0
for weights in product(range(3), repeat=len(support)):
    if not any(weights):
        continue
    probs = normalized(weights)
    demand = lambda p: sum(w for v, w in zip(support, probs) if v >= p)
    cdf = lambda p: sum(w for v, w in zip(support, probs) if v <= p)
    atom = lambda p: sum(w for v, w in zip(support, probs) if v == p)
    for p in prices:
        assert demand(p) == 1 - cdf(p) + atom(p)
        assert Q(0) <= demand(p) <= Q(1)
        for r in [Q(-2), Q(0), Q(1), Q(3)]:
            # Direct outcome accounting versus the library's formula.
            direct = sum(w * (p if v >= p else r)
                         for v, w in zip(support, probs)) - Q(1, 3)
            formula = r - Q(1, 3) + (p - r) * demand(p)
            assert direct == formula
        atomic_cases += 1
    for cutoff in support:
        # q(t)=1[t >= cutoff]; singleton cutoff values do not change dt-integrals.
        cumulative = lambda v: max(Q(0), v - max(support[0], cutoff))
        lhs = sum(w * cumulative(v) for v, w in zip(support, probs))
        breaks = sorted(set(support + [cutoff]))
        rhs = Q(0)
        for lo, hi in zip(breaks, breaks[1:]):
            mid = (lo + hi) / 2
            rhs += (hi - lo) * (1 if mid >= cutoff else 0) * demand(mid)
        assert lhs == rhs
        tail_cases += 1

uniform_cases = 0
for a, b in product([Q(-2), Q(-1), Q(0), Q(1), Q(2)], repeat=2):
    if not a < b:
        continue
    for r in [Q(-5), Q(-1), Q(0), Q(1), Q(5)]:
        candidate = max(a, min(b, (b + r) / 2))
        profit = lambda p: r + (p - r) * (b - p) / (b - a)
        assert a <= candidate <= b
        for numerator in range(17):
            p = a + Q(numerator, 16) * (b - a)
            gap = (candidate - p) * (b + r - candidate - p) / (b - a)
            assert profit(candidate) - profit(p) == gap
            assert gap >= 0
            assert (gap == 0) == (p == candidate)
            # Derivative is exactly negative net virtual-surplus weight.
            derivative = (b + r - 2 * p) / (b - a)
            net = (2 * p - b - r) / (b - a)
            assert derivative == -net
            uniform_cases += 1

print(f"PASS: {atomic_cases} atomic-demand/accounting cases; "
      f"{tail_cases} atomic tail-integral cases; "
      f"{uniform_cases} uniform price/uniqueness/derivative cases.")
