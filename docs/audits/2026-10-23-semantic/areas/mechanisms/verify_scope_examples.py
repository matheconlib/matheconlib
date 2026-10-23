"""Exact arithmetic cross-checks of rejected semantic-audit candidates.

These finite checks verify the displayed examples only. Continuity,
monotonicity on R, and universally optimal bids are justified algebraically
in the accompanying notes, not inferred from these samples.
"""

from fractions import Fraction as Q


def strict_allocation(bids):
    return tuple(int(all(x < bid for j, x in enumerate(bids) if j != i))
                 for i, bid in enumerate(bids))


# Coordinate bounds versus aggregate feasibility.
allocation = (Q(1), Q(1))
assert all(0 <= x <= 1 for x in allocation)
assert sum(allocation) > 1

# Strict highest bid discards ties and need not maximize truthful welfare.
assert strict_allocation((0, 0)) == (0, 0)
assert strict_allocation((2, 1)) == (1, 0)
assert sum(v * x for v, x in zip((0, 1), strict_allocation((2, 1)))) == 0
assert sum(v * x for v, x in zip((0, 1), (0, 1))) == 1

# Single bidder: the strict comparison over other agents is vacuous.
assert strict_allocation((-1,)) == (1,)
for bid in map(Q, [-1, 0, 1]):
    price, resale_value = Q(1), -bid
    transfer = -((price - resale_value) * bid)
    gross_expenditure = price * bid
    resale_proceeds = resale_value * bid
    assert -transfer == gross_expenditure - resale_proceeds
    assert transfer == -(1 + bid) * bid
assert -((1 - Q(1)) * Q(-1)) == 0

# Unused action gives subsidy; pairwise strategy deviations still do not.
for v in map(Q, [0, Q(1, 2), 1]):
    utility_prescribed = v * 0 - 0
    utility_unused = v * 0 - (-1)
    assert utility_prescribed == 0
    assert utility_unused == 1
    assert utility_prescribed < utility_unused

# q == 1, lower endpoint 1: canonical payment != zero-bid equilibrium payment.
for v in map(Q, [1, Q(3, 2), 2]):
    integral_one = v - 1
    canonical_payment = v - integral_one
    lowest_utility = Q(1)
    assert canonical_payment == 1
    assert canonical_payment - lowest_utility == 0
    for bid in map(Q, [0, 1, 2]):
        assert v - bid <= v

print("PASS: exact scope-example arithmetic; no generalization from samples")
