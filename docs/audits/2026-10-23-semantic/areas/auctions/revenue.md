> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Auction revenue and strict monotonicity audit

Source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`.

Inspected source files in full:

- `MathEconLib/Auction/RevenueEquivalence.lean`
- `MathEconLib/Auction/StrictMonotonicity.lean`
- `MathEconLib/Auction/IdenticalTypes.lean`

Dependencies inspected for interpretation: `Auction/Basic.lean`, `Auction/Typeclasses.lean`, `Auction/SymmetricIPV.lean`, `BidderProblem/UniversalIC.lean`. The encompassing auction audit owns their coverage records.

## Verdict

No independently verified substantive defect in the three delegated files under their full stated theorem assumptions. One independently verified standalone density-contract ambiguity is recorded below, with an explicit witness, but it does not invalidate any theorem in these files. It should not be promoted to a substantive global-density finding unless the project intends the class itself to imply a global probability density without the separately stated bounded-support assumption.

The source was not modified. This is a semantic audit, not a fresh Lean compilation claim.

## Definition and result coverage

There is one definition-like declaration in this subset, `HasPosDensity`; all other declarations are theorems or private proof lemmas. Both inclusion directions were checked for the definition. For theorems, the check is the asserted implication, not a claim that a sufficient hypothesis is necessary.

| Source | Declaration | Standard concept and equivalence/implication check |
| --- | --- | --- |
| `StrictMonotonicity.lean:42` | `HasPosDensity` | On the declared interval `[a,b]`, `F(v)=∫ₐᵛ f`, `f` continuous on `[a,b]`, `f>0` on `(a,b)`. With the separately assumed bounded type support, this is equivalent to an absolutely continuous law with a density admitting this continuous representative positive on the interval interior. See the proof below. Without bounded support it is only a local CDF representation, with a one-sided normalization at `a`. |
| `IdenticalTypes.lean:31` | `expected_sum_erase` | Linearity of expectation and identical marginals give `E[Σⱼ≠ᵢ f(Vⱼ)]=(n−1)E[f(V₀)]`. Measurability and integrability are explicit. No independence is required or inferred. The `n=1` empty-sum case is valid. |
| `RevenueEquivalence.lean:36` | `payment_formula_strictHighestBid` | The direct-mechanism envelope/payment identity with `q(v)=F(v)^(n−1)` and normalized lowest-type utility. The subtraction sign is correct for payment charged to the bidder. Independence and atomlessness arrive through `IsSymmetricIPV`. |
| `RevenueEquivalence.lean:50` | `revenue_equivalence` | Equal interim allocation functions and equal baseline utility imply equal interim payments, then identical distributions of own values imply equal ex-ante payments. Equal type bounds ensure the integration domains agree. Required composition measurability and integrability are explicit. Efficient allocation is correctly unnecessary. |
| `RevenueEquivalence.lean:86` | `total_revenue` | Efficient allocation under atomless independent identically distributed values and zero utility at the lower bound yields expected revenue equal to the second-highest value. `S₂` is the ascending order statistic indexed by `n−2`, hence the correct statistic. Bounded support gives finite integrals; the proof supplies an explicit absolute bound on interim payments. |
| `StrictMonotonicity.lean:64` | `winProb_gap` (private) | A flat strategy segment `[v₁,v₂]` implies that bidding any positive amount above the pooled bid captures at least the probability mass between the two type thresholds. The strict-highest-bid rule makes ties lose, including on positive-mass pooled bids. |
| `StrictMonotonicity.lean:94` | `ic_contradiction` (private) | A positive type cannot optimally forgo a fixed upward jump in allocation if the expected payment is continuous at the bid. The proof uses positive interior type, positive allocation gap, and nonnegative feasible deviations; all are stated. |
| `StrictMonotonicity.lean:119` | `F_strictMono_interior` (private) | A positive continuous density makes the CDF strictly increasing between interior points. The integral on `[v₁,v₂]` is positive and interval additivity gives the CDF difference. |
| `StrictMonotonicity.lean:154` | `F_pow_strict_mono` (private) | The winning-probability CDF power is strictly increasing since `n≥2`, so `n−1>0`, and the CDF is nonnegative. |
| `StrictMonotonicity.lean:167` | `strictMonotonicity` | A weakly monotone, nonnegative common strategy that is a best response against itself over all nonnegative bids, with continuous interim cost, has no flat segment and is strictly increasing on the type interval. The existing monotonicity and global cost-continuity restrictions are sufficient assumptions, not claimed necessary conditions. The proof turns any endpoint-to-endpoint flat into an interior flat, so the boundary cases are handled. |
| `StrictMonotonicity.lean:214` | `no_ties` | Injectivity on distinct interior types follows from strict monotonicity. The statement is deterministic injectivity; it does not confuse distinct-type bids with a stochastic no-tie condition. |

## Positive density: both directions in its theorem context

Let `a=lowestType`, `b=highestType`. Add `HasBoundedTypes` to the class's declared `HasIdenticalTypes` assumption. Then `F(b)=1`. The class field gives `F(a)=∫ₐᵃf=0`, so `a=b` is impossible, and bounded types imply `a≤b`; hence `a<b`.

By continuity and positivity in the interior, `f(a)≥0` and `f(b)≥0`; a negative endpoint would by continuity force a negative value at a nearby interior point. Define `g(t)=f(t)` on `[a,b]` and `g(t)=0` outside it. Then `g≥0`, it is integrable, and `∫g=∫ₐᵇf=F(b)=1`. For `v<a`, both the type-law CDF and `∫_{−∞}^v g` vanish by bounded support. For `v∈[a,b]` they agree by the defining field. For `v>b`, both equal one. Thus the probability law with density `g` has exactly the same CDF as the type law, which identifies real probability measures. The formal condition implies the intended density condition in the theorem context.

Conversely, if the type law is supported on `[a,b]` and has a density admitting a continuous representative `f` on `[a,b]` that is strictly positive on `(a,b)`, its singleton mass at `a` is zero. Thus `F(v)=∫ₐᵛ f` for every `v∈[a,b]`, while continuity and positivity are the other two fields. This supplies a `HasPosDensity` witness. Changing the density on null sets does not create a false negative: the class stores a choice of representative, so the continuous representative can be chosen.

This equivalence is to existence of a density continuous on the **closed declared interval**, positive on its interior; it does not assert that every absolutely continuous distribution or every strictly increasing CDF has this property.

## Independently verified contract ambiguity: density outside the interval

Exact location: `MathEconLib/Auction/StrictMonotonicity.lean:40–51`, especially the absence of bounded-support hypotheses at line 42 and the interval-only quantifier at lines 46–47.

Candidate semantic direction: false positive **only for a global-density reading** of the standalone class name/documentation. It is not a counterexample to the positive-density condition with bounded support assumed by `strictMonotonicity` (lines 168–174) or `no_ties` (lines 215–221).

Minimal explicit construction: take one bidder (`n=1`), a state space carrying a random variable with law

`ν = (1/2) Uniform[0,1] + (1/2) δ₂`.

For example, let the state be `(u,c)` with `u` uniform on `[0,1]`, `c` an independent fair bit, and set `θ(u,0)=u`, `θ(u,1)=2`. Use the declared bounds `[0,1]` and the zero allocation/zero transfer mechanism. All maps needed for `Auction` are measurable. `HasIdenticalTypes` is tautological for one bidder. Set the class's `f(t)=1/2` for every real `t`.

For **every** `v∈[0,1]`, including both endpoints,

`F(v) = (1/2) P(u≤v) + (1/2)·0 = v/2 = ∫₀ᵛ (1/2) dt`.

The constant density candidate is continuous on `[0,1]` and positive on `(0,1)`, so every field of the standalone class holds. Nevertheless `ν({2})=1/2`, while the Lebesgue measure of `{2}` is zero; therefore `ν` has no global Lebesgue density. `HasBoundedTypes` fails, exactly as intended by the composition of assumptions in the public theorems.

Independent verification: child verifier `verify_density` re-derived every field and both endpoints from the concrete mixture law, then used the singleton mass to refute absolute continuity, independently of this note's calculation. The parent auction auditor was informed before finalization.

Optional contract correction: either document the class as “positive continuous local CDF representation on the declared interval; combine with `HasBoundedTypes` for a density of the full law,” or require `HasBoundedTypes A` in the class's parameters. Another sufficient normalization is `F(b)=1`, since the existing equation already gives `F(a)=0`; the global density is then the zero extension from the interval. This is a contract clarification, not a proposed fix to the revenue or strict-monotonicity proofs.

## Rejected concerns and negative-case searches

- Correlated types make unconditional-opponent averages differ from economic conditional interim quantities. This is a genuine concern for standalone definitions in `Auction/Basic.lean`, passed to the owner of that file; it does not apply to the revenue results because `IsSymmetricIPV` includes mutual independence.
- A CDF that is strictly increasing but has singular mass, or a density that vanishes on a positive-measure region, is intentionally outside the positive-continuous-density condition. These are not false negatives to its stated concept.
- Nonintegrable actual transfers can make totalized interim payments economically misleading. Integrability is a dependency-level contract issue, not a new error in the payment-envelope algebra. The general revenue-equivalence theorem explicitly requires integrability of the interim-payment random variables. It does not assert a Fubini theorem about arbitrary actual transfers.
- The strict-monotonicity theorem assumes a weakly increasing strategy to begin with. This is explicit (`hreg.strategy_mono`) and is not a claim that universal IC alone yields strict monotonicity without a prior monotonicity restriction.
- `no_ties` deliberately requires unequal types. Equal types must produce equal bids under a deterministic common strategy and do not contradict it.
- The first-price bidding function is not substituted directly into `payment_formula_strictHighestBid`: this theorem concerns truthful direct mechanisms. First-price implementations can be compared through their induced direct mechanism. This is a scope restriction, not a false negative.
- Negative value intervals are allowed in the revenue theorem. Subsidies then make negative revenue possible, consistent with the payment sign convention and the second-highest-value identity. Nonnegative lower types are required only in the strict-monotonicity argument.

## Reproducible checks and verification limits

Run `python3 docs/audits/2026-10-23-semantic/areas/auctions/revenue_check.py` from the repository root. It uses exact rational arithmetic and emits `REVENUE_CHECKS_OK`.

The script checks the mixture CDF identity at five rational points and its atom mass formula; the preceding analytic argument establishes the identity for the entire continuum. It also checks the standard uniform-law formula `nE[p(V)]=(n−1)/(n+1)` for `n=2,…,10`, and the negative-support `n=2`, `Uniform[-2,-1]` value `−5/3`. These are sanity checks of encoded formulas, not proof that the general Lean theorem or this audit covers all probability laws. No claim of Lean verification is made for the mixture witness.

The economic reference for allocation-plus-baseline-utility revenue equivalence is Lawrence Ausubel's author-written [Auction Theory for the New Economy, section B](https://www.cs.cmu.edu/~sandholm/cs15-892F15/Ausubel_Auction_Theory_Palgrave.pdf). The audit uses its concept, not its assumptions as extra hidden hypotheses of the Lean theorem.

## Four-pass completion record

1. Extracted the full statements and sole new definition; mapped them to CDF density, envelope, revenue equivalence, and no-pooling concepts.
2. Rechecked against economic conventions and dependencies, including transfer sign, order-statistic index, direct-mechanism interpretation, and conditional-versus-unconditional expectation.
3. Searched false positives and false negatives: boundary types, atoms, mass outside declared bounds, pooling, singleton bidder, negative support, nonintegrable transfers, correlated types, and stronger-than-necessary regularity. The only local candidate was independently verified and appropriately downgraded.
4. Re-read all locations and proposed corrections; distinguished verified counterexample from theorem-context nonissue and finite arithmetic evidence from continuum proof. No substantive new issue remained.
