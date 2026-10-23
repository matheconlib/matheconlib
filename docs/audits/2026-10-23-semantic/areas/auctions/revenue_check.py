"""Exact algebra checks accompanying the revenue audit; not a continuum proof."""
from fractions import Fraction as Q
import json

# Mixture ν = (1/2)Unif[0,1] + (1/2)δ₂.
# The formulas below are obtained analytically from the mixture measure.
def cdf(v):
    if v < 0:
        return Q(0)
    if v <= 1:
        return v / 2
    if v < 2:
        return Q(1, 2)
    return Q(1)

points = [Q(0), Q(1, 4), Q(1, 2), Q(3, 4), Q(1)]
for v in points:
    assert cdf(v) == v / 2
assert cdf(Q(2)) - Q(1, 2) == Q(1, 2)
assert Q(1, 2) > 0

# Uniform[0,1] revenue identity for every n in a finite sanity range.
# p(v) = v^n - v^n/n = ((n-1)/n)v^n,
# n E[p(V)] = (n-1)/(n+1) = E[V_(n-1)].
revenue = {}
for n in range(2, 11):
    total_expected_payment = n * Q(n - 1, n) * Q(1, n + 1)
    expected_second_highest = Q(n - 1, n + 1)
    assert total_expected_payment == expected_second_highest
    revenue[str(n)] = str(total_expected_payment)

# Same calculation on Uniform[-2,-1], n=2: φ(v)=v²/2−2.
expected_payment_each = Q(7, 6) - 2
assert expected_payment_each * 2 == -Q(5, 3)

print(json.dumps({
    "status": "REVENUE_CHECKS_OK",
    "density_candidate_rational_checks": len(points),
    "density_candidate_atom_at_2": "1/2",
    "uniform_revenue": revenue,
    "negative_interval_revenue": str(expected_payment_each * 2),
    "limit": "Exact finite algebra checks; analytic continuum verification is in revenue.md."
}, indent=2))
