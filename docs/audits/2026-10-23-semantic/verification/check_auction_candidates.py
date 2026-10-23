#!/usr/bin/env python3
"""Independent exact checks for the explicitly encoded auction audit witnesses.

No Lean compilation is claimed. Polynomial coefficient identities are exact;
finite grids are only supplemental checks. Continuum and measure arguments are
in auction-candidates.md. Uses only Python's standard library.
"""
from fractions import Fraction as Q
from itertools import product
import json

STATES = (Q(0), Q(1))
PRIOR = {s: Q(1, 2) for s in STATES}


def mean(fn):
    return sum(PRIOR[s] * fn(s) for s in STATES)


def conditional_mean(fn, own_type):
    # Independently condition the diagonal joint law, rather than substituting
    # an assumed conditional formula.
    cells = [(weight, s, s) for s, weight in PRIOR.items() if s == own_type]
    mass = sum(weight for weight, _, _ in cells)
    assert mass > 0
    return sum(weight * fn(other) for weight, _, other in cells) / mass


def add_poly(a, b):
    n = max(len(a), len(b))
    return tuple((a[k] if k < len(a) else Q(0)) +
                 (b[k] if k < len(b) else Q(0)) for k in range(n))


def scale_poly(c, a):
    return tuple(c * coefficient for coefficient in a)


def eval_poly(p, x):
    return sum(coefficient * x**k for k, coefficient in enumerate(p))


# Payment polynomials as functions of report b, with opponent report t fixed.
# Their coefficients are reconstructed directly from c(b,t).
fp_poly = lambda t: (Q(0), 2*t - 1)
fn_poly = lambda t: (t*t, -2*t, Q(1))
fp_expected_poly = add_poly(*(scale_poly(PRIOR[t], fp_poly(t)) for t in STATES))
fn_expected_poly = add_poly(*(scale_poly(PRIOR[t], fn_poly(t)) for t in STATES))
assert fp_expected_poly == (Q(0), Q(0))
assert fn_expected_poly == (Q(1, 2), -Q(1), Q(1))

fp_payment = lambda b, t: (2*t - 1)*b
fn_payment = lambda b, t: (b - t)**2
grid = tuple(Q(k, 8) for k in range(9))
for b in grid:
    assert mean(lambda t: fp_payment(b, t)) == eval_poly(fp_expected_poly, b) == 0
    assert mean(lambda t: fn_payment(b, t)) == eval_poly(fn_expected_poly, b)
    for s in STATES:
        assert conditional_mean(lambda t: fn_payment(b, t), s) == (b-s)**2
        assert -(b-s)**2 <= 0

fp_truth_at_one = -conditional_mean(lambda t: fp_payment(Q(1), t), Q(1))
fp_deviation_to_zero = -conditional_mean(lambda t: fp_payment(Q(0), t), Q(1))
assert fp_truth_at_one == -1 < fp_deviation_to_zero == 0
fn_formal_truth_at_zero = -eval_poly(fn_expected_poly, Q(0))
fn_formal_deviation_to_half = -eval_poly(fn_expected_poly, Q(1, 2))
assert fn_formal_truth_at_zero == -Q(1, 2) < fn_formal_deviation_to_half == -Q(1, 4)

# Expected total revenue: bidder 0 payment b*t; bidder 1 payment 0.
revenue_raw = mean(lambda s: s*s)
revenue_formal = mean(lambda s: mean(lambda t: s*t))
assert revenue_raw == Q(1, 2)
assert revenue_formal == Q(1, 4)
squared_loss_revenue_raw = mean(lambda s: fn_payment(s, s))
squared_loss_revenue_formal = mean(lambda s: mean(lambda t: fn_payment(s, t)))
assert squared_loss_revenue_raw == 0
assert squared_loss_revenue_formal == Q(1, 2)

# A distinct pair of density versions, each equal to the unit-square density
# except at one singleton. Coefficient/determinant obstruction to factorization
# is algebraic and does not assume the factors have any regularity.
cube = lambda x: Q(all(0 <= coordinate <= 1 for coordinate in x))


def spike(point):
    return lambda x: Q(2) if x == point else cube(x)


corners = tuple(product(STATES, repeat=2))
density_at_origin = spike((Q(0), Q(0)))
determinant = density_at_origin((Q(0), Q(0))) * density_at_origin((Q(1), Q(1))) - \
              density_at_origin((Q(0), Q(1))) * density_at_origin((Q(1), Q(0)))
assert determinant == 1  # Product-form matrices always have determinant zero.
nonaffiliated_density = spike((Q(0), Q(1)))
x, y = (Q(0), Q(1)), (Q(1), Q(0))
join = tuple(max(a, b) for a, b in zip(x, y))
meet = tuple(min(a, b) for a, b in zip(x, y))
lhs = nonaffiliated_density(join) * nonaffiliated_density(meet)
rhs = nonaffiliated_density(x) * nonaffiliated_density(y)
assert lhs == 1 < rhs == 2
assert all(density_at_origin(x) >= 0 and nonaffiliated_density(x) >= 0 for x in corners)

# A center spike avoids any endpoint convention and gives both obstructions.
center_spike = spike((Q(1, 2), Q(1, 2)))
center_x, center_y = (Q(1, 2), Q(1, 2)), (Q(1), Q(0))
center_join = tuple(max(a, b) for a, b in zip(center_x, center_y))
center_meet = tuple(min(a, b) for a, b in zip(center_x, center_y))
center_lhs, center_rhs = center_spike(center_join)*center_spike(center_meet), center_spike(center_x)*center_spike(center_y)
assert center_lhs == 1 < center_rhs == 2
assert center_spike((Q(1, 2), Q(1, 2)))*center_spike((Q(1), Q(1))) != \
       center_spike((Q(1, 2), Q(1)))*center_spike((Q(1), Q(1, 2)))

# Private values on the supported box can fail the global predicate. At own
# signal zero exp(0)=1, so all values in this test use exact rational arithmetic.
supported_profile, unsupported_profile = (Q(0), Q(1)), (Q(0), Q(2))
v0_at_own_zero = lambda x: Q(1) + max(Q(0), x[1] - 1)
assert supported_profile[0] == unsupported_profile[0]
assert v0_at_own_zero(supported_profile) == 1
assert v0_at_own_zero(unsupported_profile) == 2

# All-purchase consequence under the same diagonal prior.
price, intercept, alpha, b = Q(1), Q(2), Q(1), Q(1)
scarcity = lambda total: intercept - alpha*total
net_payment = lambda opponent: (price - scarcity(b + opponent))*b
net_cost_formal = mean(net_payment)
net_cost_actual = conditional_mean(net_payment, Q(1))
q_formal = mean(lambda t: Q(b > t))
q_actual = conditional_mean(lambda t: Q(b > t), Q(1))
assert net_cost_formal == Q(1, 2) and net_cost_actual == Q(1)
assert q_formal == Q(1, 2) and q_actual == 0
assert q_formal - net_cost_formal == 0 and q_actual - net_cost_actual == -1

print(json.dumps({
    "result": "INDEPENDENT_EXACT_AUCTION_CHECKS_PASSED",
    "fp_expected_payment_coefficients": list(map(str, fp_expected_poly)),
    "fp_type_one_truth_and_deviation_utilities": list(map(str, (fp_truth_at_one, fp_deviation_to_zero))),
    "fn_expected_payment_coefficients": list(map(str, fn_expected_poly)),
    "fn_formal_type_zero_truth_and_deviation_utilities": list(map(str, (fn_formal_truth_at_zero, fn_formal_deviation_to_half))),
    "actual_revenue": str(revenue_raw), "formal_revenue": str(revenue_formal),
    "squared_loss_actual_formal_revenue": list(map(str, (squared_loss_revenue_raw, squared_loss_revenue_formal))),
    "origin_spike_factorization_determinant": str(determinant),
    "off_diagonal_spike_affiliation_lhs_rhs": list(map(str, (lhs, rhs))),
    "center_spike_affiliation_lhs_rhs": list(map(str, (center_lhs, center_rhs))),
    "private_values_off_support_counterexample": ["own signal 0", "rival 1: value 1", "rival 2: value 2"],
    "allpurchase_formal_actual_cost": list(map(str, (net_cost_formal, net_cost_actual))),
    "supplemental_report_grid_size": len(grid),
    "limitations": "No Lean build. Continuum quantifiers, zero-probability types, atomlessness, and null-set density equivalence use the analytic proof in the note."
}, indent=2, sort_keys=True))
