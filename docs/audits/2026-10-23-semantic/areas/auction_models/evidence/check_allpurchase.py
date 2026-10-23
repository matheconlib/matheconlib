"""Exact checks of the finite counterexample and scoped benchmark probes.

Run from the repository root with Python 3; no third-party dependencies.
This encodes a particular two-state instance, not a general theorem.
"""
from fractions import Fraction as F
import json


states = (F(0), F(1))
weights = (F(1, 2), F(1, 2))
assert sum(weights) == 1
price, intercept, alpha, bid = F(1), F(2), F(1), F(1)


def scarcity(total):
    return intercept - alpha * total


def payment(own_bid, opponent_bid):
    return (price - scarcity(own_bid + opponent_bid)) * own_bid


def winning(own_bid, opponent_bid):
    return F(own_bid > opponent_bid)


# Both type variables equal the state. Common strategy beta is identity.
profiles = [(state, state) for state in states]
assert all(0 <= v <= 1 for profile in profiles for v in profile)
assert [profile[0] for profile in profiles] == [profile[1] for profile in profiles]
mean = sum(weight * state for weight, state in zip(weights, states))
k_formal = price - intercept + alpha * mean
formal_cost = sum(weight * payment(bid, state)
                  for weight, state in zip(weights, states))
formal_q = sum(weight * winning(bid, state)
               for weight, state in zip(weights, states))
assert formal_cost == alpha * bid**2 + k_formal * bid

conditional = {}
for own_type in states:
    kept = [(weight, profile) for weight, profile in zip(weights, profiles)
            if profile[0] == own_type]
    mass = sum(weight for weight, _ in kept)
    conditional_cost = sum(weight * payment(bid, profile[1])
                           for weight, profile in kept) / mass
    conditional_q = sum(weight * winning(bid, profile[1])
                        for weight, profile in kept) / mass
    conditional[str(own_type)] = {
        "event_probability": str(mass),
        "cost": str(conditional_cost),
        "winning_probability": str(conditional_q),
        "actual_utility": str(own_type * conditional_q - conditional_cost),
        "formal_utility": str(own_type * formal_q - formal_cost),
    }
assert formal_cost == F(1, 2) and formal_q == F(1, 2)
assert conditional["1"]["cost"] == "1"
assert conditional["1"]["winning_probability"] == "0"
assert conditional["1"]["actual_utility"] == "-1"
assert conditional["1"]["formal_utility"] == "0"

# Scoped benchmark probes: these are deliberately not reported as defects.
# The source calls the Cournot expression an interior stationary candidate.
cournot_negative = 2 * (F(1) - F(2)) / (F(1) * (2 + 1))
assert cournot_negative == F(-2, 3)
# The first-best formula is explicitly an optimization over all real quantities.
phi, unit_cost, dilution = F(1), F(2), F(1)
first_best_q = (phi - unit_cost) / (2 * dilution)
first_best_w = (phi - unit_cost)**2 / (4 * dilution)
assert first_best_q == F(-1, 2) and first_best_w == F(1, 4)
# A supplied second moment need not be admissible; no such assertion is made.
eb, eb2 = F(2), F(0)
assert eb2 - eb**2 == -4

output = {
    "counterexample": {
        "price": str(price), "scarcity_intercept": str(intercept),
        "alpha": str(alpha), "own_bid": str(bid),
        "mean_purchase": str(mean), "formal_K": str(k_formal),
        "formal_cost": str(formal_cost), "formal_q": str(formal_q),
        "conditional": conditional,
    },
    "scoped_nonfindings": {
        "cournot_stationary_candidate_can_be_negative": str(cournot_negative),
        "all_real_first_best_quantity": str(first_best_q),
        "all_real_first_best_surplus": str(first_best_w),
        "arbitrary_moment_variance_expression": str(eb2 - eb**2),
    },
    "result": "ALLPURCHASE_EXACT_CHECKS_PASSED",
}
print(json.dumps(output, indent=2, sort_keys=True))
