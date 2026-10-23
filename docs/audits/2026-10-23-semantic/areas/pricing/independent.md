> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Independent hostile review: value distributions and pricing

Verdict: no confirmed semantic defect in the inspected `MathEconLib/ValueDistribution/**` definitions. This is an independent second pass, with particular attention to seemingly missing assumptions. No source files were changed.

## Definition map and equivalence conditions

| Declaration and location | Intended concept | Assessment |
| --- | --- | --- |
| `ValueDistribution`, `Basic.lean:34` | Borel probability law of a real-valued economic type | Transparent abbreviation of `ProbabilityMeasure ℝ`; exact. Negative values are allowed intentionally. |
| `ofRandomVariable`, `Basic.lean:43` | Distribution/pushforward of a random variable | `μ.map hX`; a.e. measurability is explicitly supplied. Exact, including a.e.-measurable versions. |
| `IsSupportedOnInterval`, `Basic.lean:65` | Probability-one containment in a closed interval | Exact. It does not purport to make the interval the smallest topological support. Reversed intervals cannot support a probability measure. |
| `probAtLeast`, `Demand.lean:39` | Posted-price demand with purchase at indifference | Exactly `Pr[V ≥ p]`. The weak inequality is documented, with an explicit atom correction to the CDF identity at `Demand.lean:74`. |
| `realDensity`, `Density.lean:50` | A real-valued Radon–Nikodym density representative | Correct under the explicitly documented interpretation: whole-law density only under absolute continuity; otherwise only the absolutely continuous component. Pointwise `∞ ↦ 0` and a.e. representative ambiguity are documented at `Density.lean:39–49`. |
| `expectedAllocation`, `SingleParameter.lean:51` | Integral of the allocation induced by the chosen strategy | Correct when the integrand is measurable/integrable. The unrestricted definition is intentionally Mathlib's totalized integral, and the module explicitly disclaims assumption-free economic interpretation at lines 20–29. |
| `expectedPayment`, `SingleParameter.lean:62` | Integral of payment along the chosen strategy | Same qualification. Positive payment is paid by the buyer, as documented. Bounded support and envelope IC establish the needed regularity in `ExpectedPayment.lean:196`. |
| `sellerProfit`, `SingleParameter.lean:80` | One-buyer expected payoff with continuation value and an unconditional approach cost | Formula `r − c + E[t] − r E[q]` is exact for the documented convention. An outcome-dependent acquisition cost would be another model; the documentation explicitly excludes that reading. |
| `virtualSurplusWeight`, `VirtualValue.lean:39` | Division-free weight `v f(v) − Pr[V ≥ v]` | Exact stated definition. The density relation is imposed by consuming theorems; it is not an assumption bundled into this algebraic helper. Under absolute continuity this is the usual `v f(v) − (1−F(v))`. |
| `virtualValue`, `VirtualValue.lean:50` | Chosen-density virtual value | At `f(v) ≠ 0`, algebraically equivalent to `v − Pr[V ≥ v]/f(v)`; under atomlessness, to the conventional CDF formula. Zero-density values are explicitly totalized, with the factorization theorem requiring `f(v) ≠ 0` at line 58. |
| `uniformInterval`, `Uniform.lean:42` | Uniform probability law on a nondegenerate real interval | Exactly normalized restricted Lebesgue measure; `a < b` is required. Degenerate point masses are intentionally not represented by this constructor. |
| `uniformOptimalPrice`, `UniformPricing.lean:56` | Profit-maximizing posted price restricted to `[a,b]` | Correct clipping of `(b+r)/2`. Feasible-price and distribution results impose `a < b`. Optimality and uniqueness are explicitly restricted to `[a,b]` at lines 174 and 192. |

Private `clampedAllocation` (`ExpectedPayment.lean:42`) and `tailKernel` (`TailIntegral.lean:52`) are analytic proof infrastructure, not additional economic concepts. Clamping preserves allocation on the supported type interval and supplies global measurability; the kernel encodes `lower < cutoff ≤ upper` and `cutoff ≤ value` exactly.

## Hostile tests and rejected candidates

1. **Atoms and the purchase tie.** For `Pr[V=0]=1/3`, `Pr[V=1]=2/3`, at price `1`, demand and expected payment are both `2/3`, whereas `1−F(1)=0`. This does not refute the library: `probAtLeast` uses `Ici`, and the CDF lemma adds the atom. Independently checked by direct finite sums. The same distribution with `q(t)=1[t≥1/2]` gives both sides of the density-free tail identity `1/3`: expected cumulative allocation is `(2/3)(1−1/2)`, and the tail-weighted integral is `(1/2)(2/3)`.

2. **A singular law has no whole-law Lebesgue density.** A Dirac mass at zero would make an unrestricted density-representation claim fail: its absolutely continuous component is zero but its total mass is one. This candidate is excluded by the absolute-continuity assumption in `Density.lean:68`, the expected-payment density theorem at `ExpectedPayment.lean:482`, and the seller-profit representation at `SellerProfit.lean:54`. The density documentation already distinguishes these concepts; this is not a defect.

3. **Virtual value at zero density.** For `V∼U[0,1]`, choosing `f(v)=0` makes the formal quotient zero everywhere. This is not a density of the law and is excluded by the chosen-density revenue hypotheses. Even a valid density can vanish off support: at `v=−1`, the tail is one and the weight is `−1`, while `f(v)φ(v)=0`; the factorization theorem's nonzero-density premise correctly blocks this use. The definition and module documentation explicitly describe this totalization.

4. **A.e. density agreement is insufficient for a pointwise first-order condition.** For `U[0,1]`, let `f(v)=1` except `f(1/2)=2`. This remains a valid a.e. density representative. At `v=1/2`, its formal virtual value is `(1−1/2)/2=1/4`, while the usual CDF-derivative representative gives zero. This is a real distinction between two interpretations, but the library handles it correctly: the revenue formulas are a.e. integral statements, while `PostedPriceFirstOrder.lean:53` assumes `HasDerivAt F (density price) price` pointwise. Here the required derivative is `1`, so the hypothesis with value `2` fails. The altered and original virtual values were independently recomputed using exact fractions.

5. **No-sale prices and uniqueness.** For `U[0,1]` and `r=2`, the candidate is `1`, yielding profit `2−c`; every price greater than `1` has the same profit. This does not refute uniqueness because `UniformPricing.lean:192` assumes the competing price is in `[0,1]`. Inside that interval, `r+(p−r)(1−p)` is strictly increasing up to `1`. Negative supports and continuation values also do not invalidate the formula: below-support prices sell with probability one and profit increases with price; above-support prices have zero demand and tie the upper boundary when no sale is optimal.

6. **First-order conditions are not sufficient.** A zero virtual value need not select a maximum for an irregular distribution. The theorem is explicitly necessary only (`PostedPriceFirstOrder.lean:74–78`). The separate global theorem requires an a.e. sign condition below and above the cutoff (`PostedPriceOptimality.lean:354`), and claims only optimality among posted prices in the type interval. It does not claim optimality among arbitrary mechanisms.

7. **Nonintegrable expected payment.** A heavy-tailed nonnegative payment can have infinite ordinary expectation while the totalized Bochner integral returns zero. This cannot support a reportable defect in this module without ignoring the explicit integral convention at `SingleParameter.lean:26–29`. The economic identities establish bounded-support/IC regularity before using integral linearity; the posted-price identities have bounded measurable integrands even for unbounded type distributions.

## Independent computation

The rational calculations in items 1 and 4 were checked with Python's `fractions.Fraction`, independently of Lean and the library's proof terms. A separate exact rational grid checked the uniform price formula across every integer `−3 ≤ a < b ≤ 3`, every integer continuation value `−6 ≤ r ≤ 6`, and 21 prices `p=a+(b−a)i/12`, `−4 ≤ i ≤ 16`: 5,733 price comparisons, including below-support and above-support prices. Every candidate was feasible, weakly maximized full piecewise profit on that grid, and strictly beat every distinct feasible grid price. This is bounded corroboration, not a general theorem. The general result follows directly from the concave quadratic on `[a,b]` and the outer profit pieces, matching the source's hypotheses.

The retained script is `independent_checks.py`. Reproduce from the repository root with:

```sh
python3 docs/audits/2026-10-23-semantic/areas/pricing/independent_checks.py
```

The rerun output is retained in `independent_checks.json`; its result is `all checks passed` with `exact_uniform_comparisons = 5733`.

No Lean counterexample was claimed or needed: no surviving defect candidate was identified. The report's direct finite and rational computations verify the explicit boundary examples only.
