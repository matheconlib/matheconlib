"""Exact finite sanity checks for the measure-foundations semantic audit.

These checks validate only the displayed finite encodings; they do not prove the
infinite-space Lean statements. Each encoding is described in measure.md.
"""
from fractions import Fraction as Q
from itertools import product
import json


def lr(p, q):
    return all(q[x] * p[y] <= q[y] * p[x]
               for x in range(len(p)) for y in range(x, len(p)))


def ratio_monotone(p, q):
    support = [i for i in range(len(p)) if p[i] + q[i] > 0]
    return all(Q(q[x], p[x] + q[x]) <= Q(q[y], p[y] + q[y])
               for x in support for y in support if x <= y)


nonnegative_pairs = 0
for raw in product(range(3), repeat=6):
    p, q = raw[:3], raw[3:]
    assert lr(p, q) == ratio_monotone(p, q)
    nonnegative_pairs += 1

# Ordered singleton supports: valid even though the second measure is singular
# to the first. Reversed support ordering is a positive negative-control case.
assert lr((1, 0), (0, 1))
assert not lr((0, 1), (1, 0))

# Formal relation accepts signed inputs. This does not falsify any of its
# integral theorems: their sign inequality is an algebraic determinant identity.
signed_p, signed_q = (-1, 2), (-2, 3)
assert sum(signed_p) == sum(signed_q) == 1
assert lr(signed_p, signed_q)
assert sum(i * signed_p[i] for i in range(2)) <= sum(i * signed_q[i] for i in range(2))
assert lr((-1, -1), (-1, -1))

# Zero intermediate defeats transitivity on unrestricted real functions.
p, z, r = (0, 1), (0, 0), (1, 0)
assert lr(p, z) and lr(z, r) and not lr(p, r)

# A pointwise failure caused by changing one Lebesgue-null singleton: at 0 and
# 1/2, the uniform density p is (1,1), modified q is (2,1).
assert not lr((1, 1), (2, 1))

# Check the cross-integral theorem on exact signed functions on three atoms.
# Counting measure, g=(0,1,2), finite integrability automatic.
signed_lr_cases = 0
for raw in product(range(-2, 3), repeat=6):
    p, q = raw[:3], raw[3:]
    if not lr(p, q):
        continue
    lhs = sum(i * p[i] for i in range(3)) * sum(q)
    rhs = sum(i * q[i] for i in range(3)) * sum(p)
    assert lhs <= rhs
    signed_lr_cases += 1

# A finite Giry mixture on a two-point space. Evaluate all measurable subsets.
mu0 = (Q(1, 4), Q(3, 4))
mu1 = (Q(2, 3), Q(1, 3))
outer_weights = (Q(2, 5), Q(3, 5))
mixture = tuple(outer_weights[0] * mu0[i] + outer_weights[1] * mu1[i] for i in range(2))
assert mixture == (Q(1, 2), Q(1, 2))
assert sum(mixture) == 1
for bits in product((0, 1), repeat=2):
    event_mass = sum(mixture[i] * bits[i] for i in range(2))
    barycenter_mass = sum(outer_weights[j] * sum(mu[i] * bits[i] for i in range(2))
                          for j, mu in enumerate((mu0, mu1)))
    assert event_mass == barycenter_mass

# Finite dependent-product splitting: domains of distinct sizes, each chosen
# coordinate, all tuples; exact inverse and independent-product masses.
domains = (range(2), range(3), range(1))
marginals = ((Q(1, 3), Q(2, 3)), (Q(1, 2), Q(1, 3), Q(1, 6)), (Q(1),))
split_cases = 0
for i in range(3):
    others = tuple(j for j in range(3) if j != i)
    for vector in product(*domains):
        split = (vector[i], tuple(vector[j] for j in others))
        reconstructed = tuple(split[0] if j == i else split[1][others.index(j)] for j in range(3))
        assert reconstructed == vector
        original_mass = Q(1)
        residual_mass = Q(1)
        for j in range(3):
            original_mass *= marginals[j][vector[j]]
        for j in others:
            residual_mass *= marginals[j][vector[j]]
        assert marginals[i][split[0]] * residual_mass == original_mass
        split_cases += 1

# The finite simplex correspondence and weak-dual integration evaluation.
for mass in (mu0, mu1, mixture):
    assert all(x >= 0 for x in mass) and sum(mass) == 1
    f, g = (Q(-2), Q(3)), (Q(4), Q(1))
    scalar = Q(-7, 3)
    integrate = lambda h: sum(mass[i] * h[i] for i in range(2))
    assert integrate(tuple(f[i] + g[i] for i in range(2))) == integrate(f) + integrate(g)
    assert integrate(tuple(scalar * f[i] for i in range(2))) == scalar * integrate(f)
    assert integrate((Q(1), Q(1))) == 1

# Independent-copy integral: six equally likely states, independent X and Y.
states = tuple(product(range(2), range(3)))
h = lambda x, y: Q(2 * x - y + x * y)
joint = sum(h(x, y) for x, y in states) / len(states)
iterated = sum(sum(h(x, y1) for x1, y1 in states) / len(states) for x, y in states) / len(states)
assert joint == iterated
# A deliberately dependent two-state diagonal distinguishes the two formulas.
diagonal_joint = Q(0 * 0 + 1 * 1, 2)
diagonal_iterated = Q(1, 4)
assert diagonal_joint != diagonal_iterated

result = {
    "status": "MEASURE_FINITE_CHECKS_PASS",
    "nonnegative_three_atom_lr_ratio_pairs": nonnegative_pairs,
    "signed_three_atom_lr_cases": signed_lr_cases,
    "dependent_product_split_cases": split_cases,
    "finite_giry_mixture": [str(x) for x in mixture],
    "independent_joint_integral": str(joint),
    "limitations": "Exact finite checks only; no Lean compilation or universal proof claimed.",
}
print(json.dumps(result, indent=2))
