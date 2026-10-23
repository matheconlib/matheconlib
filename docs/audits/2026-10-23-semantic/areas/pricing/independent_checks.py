#!/usr/bin/env python3
"""Independent exact checks for independent.md; no MathEconLib code imported.

This bounded calculation corroborates specified examples and a rational grid.
It does not establish the general pricing theorem or claim Lean verification.
"""

import json
from fractions import Fraction as F


def main():
    # Finite demand is computed directly from the purchase event, including ties.
    values = [F(0), F(1)]
    masses = [F(1, 3), F(2, 3)]
    price = F(1)
    demand = sum((m for v, m in zip(values, masses) if v >= price), F(0))
    expected_payment = sum(
        (m * price for v, m in zip(values, masses) if v >= price), F(0)
    )
    cdf = sum((m for v, m in zip(values, masses) if v <= price), F(0))
    atom = sum((m for v, m in zip(values, masses) if v == price), F(0))
    assert demand == expected_payment == F(2, 3)
    assert demand == 1 - cdf + atom

    # q(t)=1[t>=1/2] on [0,1]; compute the two integrals independently.
    # Its primitive from zero is max(0,v-1/2); on (1/2,1], Pr[V>=t]=2/3.
    lhs = sum(
        (m * max(F(0), v - F(1, 2)) for v, m in zip(values, masses)), F(0)
    )
    rhs = F(1, 2) * F(2, 3)
    assert lhs == rhs == F(1, 3)

    # Modify the U[0,1] density only at v=1/2. It agrees a.e. with density 1,
    # but its value 2 is not the derivative of the CDF at this point.
    value = F(1, 2)
    survival = 1 - value
    modified_phi = (value * F(2) - survival) / F(2)
    ordinary_phi = (value * F(1) - survival) / F(1)
    assert modified_phi == F(1, 4)
    assert ordinary_phi == 0

    # Check the complete piecewise demand, including prices outside support.
    comparisons = 0
    for a in map(F, range(-3, 4)):
        for b in map(F, range(-3, 4)):
            if a >= b:
                continue
            for continuation in map(F, range(-6, 7)):
                candidate = max(a, min(b, (b + continuation) / 2))

                def uniform_demand(p):
                    if p <= a:
                        return F(1)
                    if p >= b:
                        return F(0)
                    return (b - p) / (b - a)

                def profit(p):
                    return continuation + (p - continuation) * uniform_demand(p)

                assert a <= candidate <= b
                for i in range(-4, 17):
                    p = a + (b - a) * F(i, 12)
                    assert profit(p) <= profit(candidate), (a, b, continuation, p)
                    if a <= p <= b and p != candidate:
                        assert profit(p) < profit(candidate), (a, b, continuation, p)
                    comparisons += 1

    assert comparisons == 5733
    print(json.dumps({
        "atomic_demand": str(demand),
        "atomic_expected_payment": str(expected_payment),
        "atomic_tail_identity": str(lhs),
        "modified_density_phi": str(modified_phi),
        "ordinary_uniform_phi": str(ordinary_phi),
        "exact_uniform_comparisons": comparisons,
        "result": "all checks passed",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
