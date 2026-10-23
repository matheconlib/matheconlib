> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# All-purchase models: semantic audit

Source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`.
Scope: all seven `MathEconLib/Auction/AllPurchase/*.lean` files, including their
theorems and documentation. `Auction/Basic.lean`, `Auction/Typeclasses.lean`,
and `Mechanism/Auctions/AllPurchase/Spec.lean` were inspected as dependencies;
their declaration coverage belongs to other area owners.

## Result

One substantive issue appears here as a downstream instance of the auction
interim-conditioning defect: `LinearScarcityAuction.toQuadraticCostProblem`
identifies unconditional calculations with an interim problem without assuming
independence. It should be consolidated with the root finding on
`Auction.q_strat`, `p_strat`, and `toBidderProblem`, rather than counted twice.
No additional substantive defect was verified in these seven files. In
particular, pricing, welfare, and Cournot formulas have explicitly limited
algebraic or interior-stationary interpretations; feasibility and equilibrium
claims must not be inferred from their names.

This is a semantic source audit and exact finite computation, not a Lean build
claim. Source files were not changed. The independent verifier reread all seven
files and confirmed the conditional-cost witness below.

## Grouped concept coverage: every inventoried declaration

Each source location below is `MathEconLib/Auction/AllPurchase/<file>:<line>`.
“Exact” means equivalence in both directions with the stated, scoped concept,
not an implicit claim of auction equilibrium existence. Expected values use
Mathlib's totalized real Bochner integral: their ordinary finite-expectation
interpretation requires integrability. The substantive theorems that combine
them supply the necessary integrability assumptions.

| Source and declarations | Intended mathematical/economic concept | Both-direction assessment and scope |
| --- | --- | --- |
| `Basic.lean:58` `Auction.allPayBid` | Envelope payment expression `v F(v)^(n−1) − ∫_lo^v F(t)^(n−1)dt` for allocation `F(v)^(n−1)` and zero lowest-type utility. | Exact payment expression; this is not by itself an equilibrium strategy for arbitrary correlated, atomic, or negative-type auctions. For symmetric independent atomless types with strictly increasing strategy, the later allocation bridge justifies this allocation. The lowest-type lemma uses bounded atomless types. |
| `LinearScarcity.lean:50` `QuadraticCostProblem`; `:62` `LinearCostProblem` | Abstract bidder problems with global cost `α b²+K b`, `α>0`, or `p_net b`, `p_net>0`. | Exact: fields impose precisely those functional identities and coefficient signs; any such bidder problem extends to the respective structure. Neither structure asserts equilibrium. Constant scarcity is an economic limiting case; it is not admitted by the separate strictly-decreasing `AllPurchaseSpec`. |
| `LinearScarcity.lean:73` `BidderProblem.IsBoundaryRegime`; `:81` `InteriorRegimeProblem` | Lowest-type utility normalizations: `U(lo)=0`, or quadratic cost with `K<0` and `U(lo)=K²/(4α)`. | Exact relative to their explicit definitions. They do not derive a boundary/interior best response, enforce a purchase constraint, or assert full IC. The latter utility is the gain from minimizing the quadratic over all real bids and, for `K<0`, also over nonnegative bids. |
| `LinearScarcity.lean:103` `Auction.allPurchaseNetCost` | Posted expenditure minus the unconditional expected value of purchased editions at a fixed own bid. | Exact unconditional identity for finite expectations. As a genuine interim cost conditional on own information, it is not equivalent under merely identical/correlated types; see AP-C1. The definition itself does not claim conditioning in its formula. |
| `LinearScarcity.lean:117` `LinearScarcityAuction` | Auction carrying positive posted price, strict-highest allocation/no-award ties, payment `(p−φ(B))b_i`, and linear scarcity `φ(B)=φbar−α B` with `φbar,α>0`. | Exact to this specified model. Bids and scarcity values are real, including negative values, as explicitly stated in the imported specification. Nonnegative-only purchase games would require an added feasible-action domain; no such restricted model is claimed here. |
| `LinearScarcity.lean:141` `LinearScarcityAuction.meanPurchase`; `:146` `LinearScarcityAuction.K_linear` | Common unconditional mean purchase `μ=E[β(θ₀)]` and quadratic-cost coefficient `p−φbar+α(n−1)μ`. | Exact algebra for measurable integrable common strategy and identical marginals; no independence is needed for this unconditional expectation. As the coefficient of a true interim cost it is generally type-dependent under correlation; AP-C1. |
| `LinearScarcity.lean:243` `LinearScarcityAuction.toQuadraticCostProblem` | Bidder's interim decision problem under opponents' common strategy. | Fails this interpretation under its stated merely identical-type assumptions: it packages unconditional `q_strat`/`p_strat`. Exact as an unconditional opponent-law decision problem. True interim equivalence follows when own type and opponents' vector are independent; AP-C1. |
| `ExplicitSolutions.lean:56` private `AllPurchase.netCostLinear`; `:65` `AllPurchase.strategyBoundary`; `:70` `AllPurchase.strategyInterior` | Quadratic net-cost helper and positive quadratic roots selected by boundary and interior utility normalizations. | Exact formulas. With `α>0`, `K≥0`, nonnegative payment expression and bid, the boundary root uniquely solves the net-payment identity. With interior normalization and bid at least `−K/(2α)`, the interior root uniquely solves it. These are necessary algebraic consequences of IC and normalizations, not sufficient conditions for equilibrium. |
| `OptimalPricing.lean:45` `AllPurchase.interiorMeanQuantity`; `:50` `AllPurchase.sellerProfitInterior`; `:55` `AllPurchase.optimalPriceInterior` | Affine quantity formula, corresponding quadratic profit polynomial, and its unconstrained real-price maximizer. | Exact to the stated formulas. For `α>0,n≥1`, profit gap is positive coefficient times `(p−p*)²`, proving unique real maximizer. The source explicitly leaves auction-equilibrium identification, feasible regime, and economic global optimum unproved; no false positive finding is drawn from arbitrary parameters. |
| `RevenueDecomposition.lean:67` `Auction.aggregateBid`; `:71` `Auction.expectedAggregateBid` | Total purchases `B=Σ_i β(θ_i)` and its mean. | Exact for a common strategy and, for ordinary finite expectation, integrable aggregate. This does not represent heterogeneous strategies, which are outside the declared common-strategy scope. |
| `RevenueDecomposition.lean:75` `Auction.sellerGrossRevenue`; `:79` `Auction.expectedEditionValue`; `:84` `Auction.expectedNetPayment` | Gross posted-price receipts `p E[B]`, aggregate edition value `E[Bφ(B)]`, and net bidder expenditure `E[Σ_i(p−φ(B))b_i]`. | Exact. Gross seller receipts and bidder net expenditure differ by edition value; the code distinguishes them correctly. The supplied-integrability accounting theorem expresses their sum. |
| `RevenueDecomposition.lean:93` `Auction.expectedAllPayBid`; `:100` `Auction.lowestTypeUtility`; `:108` `Auction.allPayBenchmarkProfit` | Expected envelope bid under bidder 0's common marginal; bidder 0's lowest-type utility; benchmark total all-pay revenue. | Exact as marginal benchmark calculations. Lowest-type utility becomes common only with the explicitly supplied equal-utility condition. Its true interim interpretation inherits AP-C1 outside independent types. The decomposition theorem itself assumes independence and is not refuted by AP-C1. |
| `RevenueDecomposition.lean:113` `Auction.editionsOnlyBenchmarkProfit`; `:118` `Auction.bundledProfit` | `(p−c) B_ed` at a supplied editions-only quantity and `(p−c) E[B]` for bundled purchases. | Exact profit expressions for posted receipts minus constant unit production cost. No optimizing/equilibrium property is required of the supplied benchmark quantity. |
| `RevenueDecomposition.lean:603` `LinearScarcityAuction.cournotQuantityLinear` | Interior stationary symmetric total quantity `n(φbar−p)/(α(n+1))` for buyer payoff `b_i(φbar−αB−p)`. | Exact to the stated interior-stationary concept; for nonnegative purchases the Nash quantity is this expression only if `φbar≥p`, and otherwise zero. The source states infeasibility for `φbar<p`, so the missing truncation is not a defect of this scoped definition. |
| `WelfareDecomposition.lean:61` `AllPurchase.editionWelfare` | Aggregate edition value less production cost, `(φbar−c)B−αB²`. | Exact for total scarcity value `Bφ(B)`; it is not the integral under an inverse demand curve. Scarcity changes the value of every edition, so the aggregate expression includes the full dilution externality. |
| `WelfareDecomposition.lean:66` `AllPurchase.firstBestQuantity`; `:70` `AllPurchase.firstBestEditionSurplus` | All-real-quantity quadratic welfare optimizer and optimum for `α>0`. | Exact under `α>0`; squared-completion gap proves it. The code explicitly says optimization over all real quantities and feasibility iff `φbar≥c`. For a nonnegative-only model use `max 0 ((φbar−c)/(2α))` and `(max 0 (φbar−c))²/(4α)`. No such restricted interpretation is claimed. |
| `WelfareDecomposition.lean:99` `AllPurchase.cournotLoss`; `:105` `AllPurchase.contestLoss` | Welfare differences through a supplied intermediate benchmark: `W*−W(B_ed)` and `W(B_ed)−WC`. | Exact algebraic differences in both directions. They require actual Cournot/bundled values for economic labels, and do not claim either difference is nonnegative; source is explicit. |
| `WelfareDecomposition.lean:120` `AllPurchase.bundledEditionWelfareMoments` | Quadratic expected welfare expressed in two supplied moments. | Exact algebra; ordinary expected-welfare interpretation requires that the numbers really are the first and second moments of a square-integrable quantity. Source explicitly states this. |
| `WelfareDecomposition.lean:146` `LinearScarcityAuction.expectedAggregateBidSq`; `:153` `LinearScarcityAuction.bundledEditionWelfare` | Second moment of total purchases and moment-form expected edition welfare. | Exact for integrable `B,B²`; the bridge to `E[Bφ(B)]−c E[B]` supplies both hypotheses. Without integrability these are totalized expressions, and the source labels the latter as a moment expression. |

## AP-C1: unconditional opponent averaging is misidentified as interim

**Locations.** `LinearScarcity.lean:239–253`, especially the definition at
`:243` and the inherited `A.toBidderProblem` at `:248`; related cost and
coefficient formulas at `:103–106`, `:141–147`, and `:231–237`. The root is
`MathEconLib/Auction/Basic.lean:99–108` and `:198–213`.

**Minimal explicit instance.** Two bidders and two equally likely states
`ω∈{0,1}`. Both types are exactly `θ₀(ω)=θ₁(ω)=ω`, the common strategy is
`β(v)=v`, the declared bounds are `[0,1]`, price is `p=1`, and scarcity is
`φ(B)=2−B` (`φbar=2`, `α=1`). Allocate the prize precisely to a strictly highest
bidder, awarding no prize on a tie, and set transfers to the required negative
net payments. The probability space is finite with full powerset sigma-algebra.

All hypotheses of the conversion are met: the common type variables are
identical in distribution, all functions are measurable, the two strategy
purchases are integrable, price/intercept/dilution are positive, scarcity is
continuous and strictly decreasing, and the strict-highest outcome coordinates
are Borel measurable. The types are correlated; independence is not assumed.

At own bid `b=1`, the formal unconditional mean of the opponent's bid is `1/2`.
Thus `K_linear=1−2+1/2=−1/2`, formal cost is `1−1/2=1/2`, and formal winning
probability is `P(1>θ_j)=1/2`. For own type `v=1`, the packaged bidder problem
therefore assigns utility `1·(1/2)−1/2=0`.

But conditional on own type `1` (an event of probability `1/2`), the opponent
surely has type and bid `1`. Total purchases are `2`, scarcity value is `0`,
payment is `(1−0)·1=1`, and the tied bidder never wins. Actual interim utility
is `1·0−1=−1`. This is not a zero-probability-conditioning ambiguity.

**Why this is a semantic defect rather than a false theorem.** The polynomial
identities hold exactly for the unconditional quantities defined by the code.
The definition's advertised *interim* economic interpretation is incorrect
without a conditional opponent law or independence. The revenue-decomposition
results later assume independence; this example does not refute those results.

**Correction.** Require `HasIndependentTypes` when presenting the conversion as
an interim problem, or use type-dependent conditional allocation and cost. For
linear scarcity the correct coefficient is
`K_i(v)=p−φbar+α E[Σ_{j≠i} β(θ_j) | θ_i=v]`.
The conditional model generally needs the own type as an extra argument and
cannot use a single type-independent `BidderProblem.cost` without further
restrictions. A purely unconditional conversion may remain with an explicit
unconditional name and interpretation.

**Verification.** The exact rational calculation is preserved in
`evidence/check_allpurchase.py`; its run produced
`evidence/allpurchase-results.json` with token
`ALLPURCHASE_EXACT_CHECKS_PASSED` and exit status 0. A separate verifier
independently recomputed the probabilities, payments, utilities, and all
hypotheses, reaching the same result. This computation encodes only this finite
instance; the strict anti-monotonicity and measurable-allocation hypotheses are
checked analytically above.

## Theorem bridge and hostile-review checks

- `Basic.lean:63,72`: zero envelope bid at the lower bound uses `F(lo)=0` and
  `n−1>0`; monotonicity gives the integral's measurable primitive.
- `UniformDistribution.lean:40`: on `[0,vbar]`, `F(t)=t/vbar`, `lo=0`, and
  `vbar>0`; integrating `t^(n−1)` yields `(n−1)v^n/(n vbar^(n−1))`.
- `LinearScarcity.lean:155,183,203,231`: linearity of integrable unconditional
  expectations yields the stated quadratic; no false independence premise is
  needed for the algebra, only for its true interim reading.
- `ExplicitSolutions.lean:74,90,111,124,137,166,178,220,244`: completed-square
  and quadratic-root manipulations were checked with signs and root-selection
  premises. The interior lower-root ambiguity is explicitly excluded.
- `RevenueDecomposition.lean:126,178,194,211`: strict monotonicity, bounded
  atomless independent identical types justify the own-bid threshold and
  `F(v)^(n−1)` allocation; equality at the lower endpoint is handled.
- `RevenueDecomposition.lean:244,263,291,368,450,482,517,567,617`: pointwise
  net/gross accounting, Fubini under independence, envelope/IC, and finite-sum
  integration have the needed integrability hypotheses. The source-formula
  discrepancy documented at `:510–515` is not silently promoted to a theorem.
- `OptimalPricing.lean:62,83,95,102,113,134`: the coefficient `n/(α(n+1))` is
  positive exactly under the supplied signs and `n≥1`; the maximizer follows
  from its square gap. The regime equivalence is algebraic only.
- `WelfareDecomposition.lean:74,83,111,126,160,183`: welfare square completion,
  telescoping gap, variance expression, and integral linearity are correct with
  their stated signs and moment assumptions.

Explicit discarded leads are reproducible in the verification script:
`φbar=1,p=2,α=1,n=2` gives negative stationary Cournot quantity `−2/3`,
`φbar=1,c=2,α=1` gives the all-real first-best quantity `−1/2`, and supplied
moments `EB=2,EB2=0` give a negative putative variance. Each is outside the
economic interpretation explicitly excluded in the respective docstring,
so none is reported as a defect.

## Four-pass completion record

1. Read all seven complete sources, inventory definitions, imported mechanism
   specification, auction base quantities, and environment typeclasses.
2. Map every definition to its economic/algebraic concept and audit both
   implications under the exact declared scope; inspect bridge hypotheses.
3. Seek correlated information, sign/zero/negative-quantity, missing moment,
   tie, and wrong-root counterexamples; independently verify AP-C1 and discard
   probes that attack explicitly disclaimed interpretations.
4. Reread source locations and table against inventory, rerun exact witness,
   and incorporate the independent full-scope review. No additional change
   to the semantic conclusions emerged in the last pass.
