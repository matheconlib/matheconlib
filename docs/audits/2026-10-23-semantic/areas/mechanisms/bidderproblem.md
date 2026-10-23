> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# BidderProblem semantic audit

Scope: all four files in `MathEconLib/BidderProblem`, all 11 definitions,
structures, and classes. Source files were read without modification. This
note distinguishes the reduced, single-bidder interim problem from the
original many-bidder auction.

## Result

No substantive defect in the formal definitions was established. The
definitions match the stated quasilinear single-parameter reduced model.
There are two terminology/normalization caveats below; neither invalidates
the associated formal definitions or proved payment identities.

## Definition coverage

| Definition and source | Intended concept | Equivalence and boundary checks |
|---|---|---|
| `BidderProblem`, `Basic.lean:24–36` | A real-action, quasilinear interim decision problem with prescribed candidate strategy | `winProb` is in `[0,1]`, and cost is a real payment that may include subsidies. These are exactly the required reduced data. No IC, feasibility, or equilibrium claim follows from constructing the data alone. The comment calling `strategy` an equilibrium bidding strategy should be understood as a candidate strategy until IC is supplied. |
| `typeInterval`, `Basic.lean:43` | Closed type interval | Exactly `Icc lowestType highestType`. The structure does not require ordered endpoints: reversed endpoints produce the empty type set and vacuous IC. This is mathematically consistent with the specified set, although applications requiring actual types must establish nonemptiness. Singleton endpoints are allowed. |
| `payoff`, `Basic.lean:47` | Risk-neutral interim quasilinear expected utility | Exactly `v × winning probability − expected payment`. It correctly permits negative payments; it deliberately does not describe risk aversion, nonlinear value of allocations, or type-dependent payment disutility. |
| `q`, `Basic.lean:48` | Allocation probability induced by the prescribed strategy | Exactly `winProb(strategy(v))`. No averaging over bidder types occurs here; the interim averaging is already embodied in `winProb`. |
| `U`, `Basic.lean:49` | Utility induced by the prescribed strategy | Exactly `payoff(v,strategy(v))`. It is an optimized value function only when an appropriate IC assumption is present. |
| `toSingleParameterProblem`, `Basic.lean:70–76` | Specialize the action-parametric single-parameter model to real bids | The conversion retains every mathematical field, including both endpoints, allocation, payments, and strategy. All compatibility lemmas are definitional equalities; there is no loss or enlargement of the action domain. |
| `IsRegular`, `Basic.lean:122–126` | Custom shape assumptions used by auction equilibrium results | Exactly global allocation monotonicity, strategy monotonicity and nonnegativity on the type interval, and continuous costs. This is a bundled regularity assumption, not Myerson distributional regularity and not by itself an equilibrium assertion. The auction strict-monotonicity theorem separately requests universal IC (`Auction/StrictMonotonicity.lean:173–174`). |
| `HasEnvelopeIC`, `EnvelopeIC.lean:47–49` | Supporting-hyperplane/subgradient form of reduced IC | Exactly equivalent to type-deviation IC by the algebra below. Quantification over *all ordered pairs* supplies both incentive directions, including decreasing type changes. It is stronger than merely asserting an a.e. envelope derivative formula. |
| `HasTypeDeviationIC`, `TypeDeviationIC.lean:46–48` | Truthful IC of the induced direct, one-agent mechanism; equivalently no profitable imitation of another type's prescribed bid | The inequality is exactly the deviation payoff comparison. Deviations are restricted to strategy-generated actions; all unrestricted feasible-action deviations belong to `HasUniversalIC`. Calling it DSIC is valid for this induced one-agent direct mechanism. It does not by itself establish ex-post DSIC of the original many-bidder auction from interim probabilities and payments. |
| `allPayBid`, `TypeDeviationIC.lean:119–120` | Canonical payment normalized to zero utility at the lower type | Exactly `v*q(v) − ∫ lowestType..v, q`. In a genuine all-pay implementation with zero lowest-type utility this is the bid/payment. For another utility normalization, actual expected payments differ by the explicit constant in `netPaymentIdentity` (`:131–135`). It is defined on all real `v`, but the IC and payment conclusions concern the stated type interval. |
| `HasUniversalIC`, `UniversalIC.lean:43–46` | Optimal feasible bid for each type | Exactly feasibility of the prescribed action plus weak payoff dominance over every feasible action in the same specified set `S`. The feasibility clause prevents the common false positive in which an infeasible action outperforms every feasible alternative. It need not compare actions outside `S`. |

## Two-direction checks and rejected defects

Write `p(s) = cost(strategy(s))`, `q(s) = winProb(strategy(s))`, and
`U(s) = s*q(s) − p(s)`. For every ordered pair `s,t`,

```
(s−t)*q(t) ≤ U(s)−U(t)
iff
s*q(t)−p(t) ≤ s*q(s)−p(s).
```

This proves both directions of equivalence between `HasEnvelopeIC` and
`HasTypeDeviationIC`. Thus no object can distinguish the two conditions.
The descriptions “Level 0”, “middle IC level”, and “weakest” do not establish
three strictly distinct strengths: the two lower levels are equivalent.
Proposed documentation correction: describe them as equivalent reduced-IC
formulations and optionally provide the missing reverse conversion theorem.
This is a terminology/API issue, not a substantive false-positive defect.

The analogous distinction between type-deviation and universal IC is real.
For example, on types `[0,1]`, let every type bid `0`, let every bid have
winning probability `0`, and let `cost(b) = −1` when `b = 1` and `0`
otherwise. Type deviations cannot change the chosen bid, so both reduced
IC conditions hold. With `S = {0,1}`, bid `1` improves payoff from `0` to
`1`, so universal IC fails. This is intended behavior, not a defect.

For the normalization caveat, take a single bidder, type interval `[1,2]`,
winning probability identically `1`, all-pay cost `cost(b)=b`, feasible bids
`[0,∞)`, and strategy identically `0`. Every type optimally bids zero:
`v−b ≤ v` for all `b≥0`; `U(1)=1`. Nevertheless the definition gives

```
allPayBid(v) = v − ∫₁ᵛ 1 = v − (v−1) = 1.
```

This refutes an *unqualified* interpretation of the docstring phrase
“standard all-pay auction equilibrium bid function” (`TypeDeviationIC.lean:117–118`).
It does not refute the normalized definition: the exact identity already
proved in the source gives `cost(strategy(v)) = 1−U(1)=0` correctly.
Proposed documentation correction: call it the canonical zero-lowest-utility
payment, and qualify the equilibrium interpretation with the normalization
or the usual atomless, at-least-two-bidder assumptions giving `q(lowestType)=0`.
No substantive finding is reported from this example because the formal
definition and explicit payment-normalization identity are consistent.

## Verification record

All payoff comparisons and the two-direction reduced-IC equivalence were
independently expanded from the source definitions. SageMath independently
verified the exact polynomial identity and constant-polynomial integral,
without numerical approximation or bounded sampling:

```python
R = PolynomialRing(QQ, names=('v','t','qv','qt','pv','pt','b','x'))
v,t,qv,qt,pv,pt,b,x = R.gens()
E = (v*qv-pv) - (t*qt-pt) - (v-t)*qt
I = (v*qv-pv) - (v*qt-pt)
assert E == I
F = R(1).integral(x)
assert v - (F.subs({x:v}) - F.subs({x:R(1)})) == 1
assert (v-b) - v == -b
```

The Sage command exited successfully. A standalone LeanProbe check timed
out during environment initialization after 120 seconds; no Lean
certification is claimed. No source changes were needed and no generalized
claim is inferred from a finite computation.
