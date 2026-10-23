"""Exact finite-law checks for the auction semantic audit.

Run with Python 3; no third-party dependencies.  Probability space: two equally
likely states 0,1, with both bidder values equal to the state.  Bidder 1 always
has zero allocation/payment.  Bidder 0 also has zero allocation, so utility is
minus payment.  Polynomials below use coefficient tuples in increasing order.
Coefficient identities certify the marginal formulas for ALL real reports;
point evaluations certify the specific witnesses.  Nonnegativity of squares
is the analytic argument for all deviations in witness B.
"""

from fractions import Fraction as Q


def average_polynomials(*polynomials):
    return tuple(sum(p[k] for p in polynomials) / len(polynomials)
                 for k in range(len(polynomials[0])))


def evaluate(coeffs, value):
    return sum(c * value ** k for k, c in enumerate(coeffs))


def true_expected_payment(payment):
    return sum(payment(s, s) for s in (Q(0), Q(1))) / 2


# A. Payment (2t-1)b; each marginal polynomial is +/-b.
a_marginal = average_polynomials((Q(0), Q(-1)), (Q(0), Q(1)))
assert a_marginal == (Q(0), Q(0))
a_payment = lambda b, t: (2 * t - 1) * b
assert -a_payment(Q(1), Q(1)) == -1
assert -a_payment(Q(0), Q(1)) == 0
print("A: marginal payment identically 0; true type 1 utility: truth -1, bid 0: 0")

# B. Payment (b-t)^2; marginal .5[b^2+(b-1)^2].
b_marginal = average_polynomials((Q(0), Q(0), Q(1)),
                                (Q(1), Q(-2), Q(1)))
assert b_marginal == (Q(1, 2), Q(-1), Q(1))
b_payment = lambda b, t: (b - t) ** 2
for s in (Q(0), Q(1)):
    assert b_payment(s, s) == 0
assert -evaluate(b_marginal, Q(0)) == Q(-1, 2)
assert -evaluate(b_marginal, Q(1, 2)) == Q(-1, 4)
# Algebraic square completion, valid for every real report.
square_completed = (Q(1, 4) + Q(1, 4), Q(-1), Q(1))
assert b_marginal == square_completed
print("B: marginal payment b^2-b+1/2 = (b-1/2)^2+1/4")
print("B: conditional truthful payment 0 at each state; all deviations cost a square")
print("B: formal type 0 utility: truth -1/2, bid 1/2: -1/4")

# C. Payment bt; true law uses t=s, nested marginal expectation uses a fresh t.
c_marginal = average_polynomials((Q(0), Q(0)), (Q(0), Q(1)))
assert c_marginal == (Q(0), Q(1, 2))
c_payment = lambda b, t: b * t
c_actual = true_expected_payment(c_payment)
c_formal = sum(evaluate(c_marginal, s) for s in (Q(0), Q(1))) / 2
assert c_actual == Q(1, 2)
assert c_formal == Q(1, 4)
print(f"C: actual expected revenue {c_actual}; defined expectedRevenue {c_formal}")

print("PASS: exact coefficient and finite-law checks; no library compilation claimed")
