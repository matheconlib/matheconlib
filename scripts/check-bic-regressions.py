#!/usr/bin/env python3
"""Independent exact arithmetic for the BIC regressions; Lean proves continuum claims.

Run from the repository root: python3 scripts/check-bic-regressions.py
No floating point arithmetic or third-party packages are used. Finite report
checks here supplement, rather than replace, the real-report Lean proofs.
"""

from fractions import Fraction as F
from itertools import product


def expectation(prior, f):
    return sum((probability * f(state) for state, probability in prior.items()), F(0))


correlated = {(0, 0): F(1, 2), (1, 1): F(1, 2)}
independent = {state: F(1, 4) for state in product((0, 1), repeat=2)}
reports = (F(0), F(1, 2), F(1))


def bad_payment(bids):
    return (2 * bids[0] - 1) * (2 * bids[1] - 1)


def square_payment(bids):
    return (bids[0] - bids[1]) ** 2


def updated(state, i, report):
    return tuple(report if j == i else state[j] for j in range(2))


for i in range(2):
    for s in (F(0), F(1)):
        posterior = {state: F(1) for state in correlated if state[i] == s}
        truthful = expectation(posterior, lambda state: -bad_payment(state))
        lying = expectation(posterior, lambda state: -bad_payment(updated(state, i, 1 - s)))
        assert truthful == -1 and lying == 1
        for r in reports:
            assert expectation(correlated, lambda state: bad_payment(updated(state, i, r))) == 0
            utility = expectation(posterior, lambda state: -square_payment(updated(state, i, r)))
            assert utility == -(r - s) ** 2 <= 0
        marginal_truth = expectation(correlated, lambda state: -square_payment(updated(state, i, s)))
        marginal_half = expectation(correlated, lambda state: -square_payment(updated(state, i, F(1, 2))))
        assert marginal_truth == -F(1, 2) < marginal_half == -F(1, 4)

assert expectation(correlated, lambda state: 2 * bad_payment(state)) == 2
assert expectation(correlated, lambda state: 2 * square_payment(state)) == 0
assert correlated[(0, 0)] != F(1, 2) * F(1, 2)

# Independently expand the expected squared payment as polynomial coefficients
# in increasing powers of the report: (b^2 + (b-1)^2)/2.
assert tuple((a + b) / 2 for a, b in zip((F(0), F(0), F(1)),
                                      (F(1), F(-2), F(1)))) == (F(1, 2), F(-1), F(1))


def posted_payment(bid):
    return F(1, 4) if bid >= F(1, 2) else F(0)


def posted_allocation(bid):
    return F(1, 2) if bid >= F(1, 2) else F(0)


for s in reports:
    for r in reports:
        assert s * posted_allocation(s) - posted_payment(s) >= s * posted_allocation(r) - posted_payment(r)

assert expectation(independent, lambda state: sum(posted_payment(bid) for bid in state)) == F(1, 4)
assert F(1, 2) * (1 - F(1, 2)) == F(1, 4)  # area under the allocation curve

# A separate opponent-sensitive payment checks the joint/marginal revenue
# identity's arithmetic under independence, independently of own-report prices.
actual = expectation(independent, lambda state: 2 * state[0] * state[1])
nested = sum(expectation(independent, lambda state: expectation(
    independent, lambda opponents: updated(opponents, i, state[i])[0]
    * updated(opponents, i, state[i])[1])) for i in range(2))
assert actual == nested == F(1, 2)

print("BIC exact arithmetic checks passed")
