> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Auction core semantic audit

Source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`. Source files were read without changes. Locations below refer to this revision. This note covers all 23 inventoried declarations in `Auction/Basic.lean` and `Auction/Typeclasses.lean`; the companion notes cover the other five assigned files.

## Pass 1: inventory and intended concepts

| Declaration and exact source location | Standard concept and assessment in both directions |
| --- | --- |
| `Auction`, Basic:66–79 | A common-prior, single-parameter, private-value, quasilinear mechanism environment with real messages. The data exactly encode measurable type random variables, measurable allocations, transfer rules, and declared bounds. No feasibility, support containment, payment measurability, or integrability is bundled; the docstring explicitly separates these. A standard environment with these data constructs this structure; arbitrary inhabitants need the additional conditions before receiving the corresponding economic interpretation. This is a generic environment structure, not a claim of single-good feasibility. |
| `interval`, Basic:87 | The declared closed type interval. Exactly `Icc θmin θmax` in either direction. Without bounded types its endpoints need not bound realized values, and the interval can be empty; both are deliberate unbundled restrictions. |
| `q_strat`, Basic:99–100 | Marginal expected allocation against opponents following a **common** strategy. Exactly this expectation when integrable, with Bochner totalization otherwise. It is a standard *conditional interim* allocation only when the opponents' conditional law given own type equals their marginal law; see C1. Conversely a genuine correlated interim allocation need not equal this quantity. Common strategy rather than a bidder-specific strategy profile is an explicit restriction. |
| `p_strat`, Basic:107–108 | Marginal expected payment against opponents' common strategy, with payment equal to negative transfer. Sign convention is correct. Integrability and conditional-law qualifications parallel `q_strat`; neither unconditional independence nor payment integrability is assumed. |
| `q`, Basic:128 | Truthful-opponent specialization `q_strat id`. Exact in both directions as a marginal expectation; conditional interim interpretation fails on correlated types. |
| `p`, Basic:131 | Truthful-opponent specialization `p_strat id`. Exact marginal expectation on integrable slices; conditional interpretation fails on correlated types. |
| `U`, Basic:134 | `s q(s) − p(s)` is marginal truthful-report utility, and conditional expected truthful utility under independence plus integrability. It is not that conditional utility in general; C1 gives both semantic directions. |
| `ExPostIR`, Basic:175–177 | Quasilinear truthful utility nonnegative for every profile in the product of declared intervals. Formal and standard ex-post IR on that product are identical. This is the full-product convention, not merely almost-sure IR on joint support. No integrals occur, so correlation and payment totalization do not affect this predicate. |
| `InterimIR`, Basic:181–182 | Nonnegative utility for every declared type. Equivalent to standard interim IR with independent types, integrable slices, and the same all-types convention. Under the actual generic hypotheses neither direction holds; C1-A and C1-B. |
| `ExAnteIR`, Basic:185–187 | Nonnegative expected truthful quasilinear utility before learning own type. Exact in both directions when the integrand is integrable, without independence. For nonintegrable utilities it is the documented totalized real integral rather than ordinary expected utility. |
| `BIC`, Basic:192–194 | Truthful direct revelation is an interim best reply against truthful opponents, with reports restricted to the declared type interval. Exact under independent types and integrable allocation/payment slices. Under the actual generic hypotheses both directions fail; C1-A and C1-B. The restriction to type reports is the usual direct-mechanism convention; this predicate does not claim best response to every real bid outside that domain. |
| `toBidderProblem`, Basic:206–213 | Single-agent decision problem induced by opponents' common strategy and marginal averaging. The translation copies type bounds, allocation, payment, strategy exactly and proves allocation lies in `[0,1]`. It coincides with the actual Bayesian bidder problem under independence and suitable integrability; C1 invalidates that interpretation without independence. |
| `HasIndependentTypes`, Typeclasses:29–30 | Mutual independence of all type random variables. Exact standard mathematical definition via `iIndepFun`; both directions hold. This is stronger than pairwise independence, as intended. |
| `HasIdenticalTypes`, Typeclasses:33–36 | Equal marginal type laws together with equal declared endpoints. Exact in both directions for the documented combination. Equal laws alone need not imply equal arbitrary declared bounds, so that narrower concept is deliberately not its contract. No strategy symmetry is claimed. |
| `HasBoundedTypes`, Typeclasses:39–40 | Pointwise containment of every realized value in its declared interval. Exact under that pointwise convention. Standard almost-sure boundedness can differ by a null state, an intentional modeling restriction of the explicitly quantified field. |
| `HasDensity`, Typeclasses:43–44 | Each type law is absolutely continuous with respect to Lebesgue measure, expressed by `HasPDF`. Exact in both directions for measurable real random variables. Does not assert a positive or continuous density. |
| `HasAtomlessTypes`, Typeclasses:47–48 | Purports to mean atomless types, but tests only bidder `0`. All-bidder atomlessness implies the field, but the converse requires `HasIdenticalTypes` or `n=1`; C3. |
| `IsSymmetricIPV`, Typeclasses:53–55 | Convenience bundle for mutually independent, identically distributed, pointwise bounded types with density and no atoms. The five bundled properties are exactly equivalent to its fields. General symmetric IPV need not have density or bounded support, but the docstring explicitly says all five properties are bundled: this is a smooth bounded subclass, not a counterexample. Private values/quasilinearity come from the auction utility specification. Equal laws make the bidder-0 atomlessness issue harmless inside this bundle. |
| `lowestType`, Typeclasses:61 | Common declared lower endpoint under identical bounds. Exact in both directions. It need not be the essential infimum: declared bounds need not be tight. This matches the documented endpoint interpretation. |
| `highestType`, Typeclasses:67 | Common declared upper endpoint, with the same qualification. |
| `commonCDF`, Typeclasses:80–81 | Right-continuous CDF of the common type law, `P(θ₀≤s)`. Equal laws make it the CDF of every bidder. Exact in both directions. |
| `HasZeroLowestTypeUtility`, Typeclasses:141–142 | Zero utility at the common declared lower endpoint, not an IR condition. Exactly the stated normalization; docs explicitly distinguish participation predicates. Its utility inherits C1's generic conditioning restriction. |
| `expectedRevenue`, Typeclasses:145–146 | Expected sum of **marginally averaged** per-type payments. This is expected total seller revenue under independence and joint integrability/Fubini conditions. Under the actual unrestricted hypotheses it can undercount or overcount even finite, integrable actual revenue; C2. |

## Pass 2: concept and theorem checks

Interim information includes own type. Under a joint prior the expectation in every deviation comparison must use the opponents' law **conditional on the same true type**, including when the reported type changes. [Arunava Sen's mechanism-design lectures, Definition 10](https://www.isid.ac.in/~asen/scdoc/iisclectures.pdf) state this conditional-prior formulation; its indexed PDF text was retrieved by web search (direct PDF fetch timed out). [Dirk Bergemann's Yale lectures on correlated types, pp. 2–4](https://campuspress.yale.edu/dirkbergemann/files/2012/01/lecture2yale2012.pdf) explain posterior type beliefs and the failure of ordinary independent-type revenue equivalence after allowing correlation. The counterexamples below were derived from the definitions; they do not depend on a cited theorem.

All helper lemmas in Basic were inspected. `q_strat_range` is correct for the totalized integral even for nonmeasurable strategies: a nonintegrable allocation integral is zero, and zero lies in `[0,1]`. This is not an integrability theorem. The separately named measurability/integrability lemmas have the needed measurable-strategy and allocation bounds. `payment_formula` and `payment_equivalence` are algebraically valid theorems about the formal one-dimensional marginal IC problem; C1 concerns their economic interpretation when a generic correlated environment is called BIC. Typeclasses' CDF boundary lemmas correctly combine support, equal bounds, and no atoms of the common law. The lowest-type zero normalization is correctly distinguished from IR.

## Pass 3: explicit substantive candidates

### C1 — Missing conditioning changes BIC and interim IR in both directions

Locations: `Basic.lean:99–108,128–134,181–194,206–213`. Main predicate sites are lines 181–182 and 192–194. Severity: major conceptual contract defect in generic auction environments.

Common setup: two bidders, `Ω={0,1}`, each state probability `1/2`, `θ₀(ω)=θ₁(ω)=ω`, both intervals `[0,1]`. Allocation is identically zero for both bidders. Bidder 1 pays zero. Bidder 0's payment is one of the polynomials below, in own report `b` and opponent report `t`; set the mechanism transfer to its negative. The allocation and type maps are measurable, all displayed payments and utilities are finite/integrable on this probability space, the allocation is feasible, and both realized values are in their intervals. Every report considered belongs to `[0,1]`.

**False positive, C1-A:** let `c₀(b,t)=(2t−1)b`. The formal payment is

`p₀(b) = [−b+b]/2 = 0`

for **every real** `b`. Thus formal `q₀=0`, `U₀=0`; bidder 1 also has zero utility. Both `A.BIC` and `A.InterimIR` hold for **all** real types/reports in the full interval, not just endpoints. But own type `1` reveals opponent type `1`. Its truthful utility is `−c₀(1,1)=−1`, whereas reporting `0` gives `0`. Both genuine interim IR and BIC fail at a positive-probability type. Actual ex-ante utility is `−1/2`, and `ExAnteIR` correctly rejects it; the familiar interim-IR-implies-ex-ante-IR implication is broken by this incorrect interim definition.

**False negative, C1-B:** let `c₀(b,t)=(b−t)²`. At each realized own type `s∈{0,1}`, the opponent is `s`, so truth costs zero and every report `b∈[0,1]` has utility `−(b−s)²≤0`. Thus the actual mechanism is BIC and interim IR for both possible types against **all** real reports in the interval. To impose an all-declared-types convention even at zero-probability interior types, the regular conditional kernel `t|s=δ_s` is a valid version for this finite law and gives the same conclusion for every `s∈[0,1]`. The formal marginal payment instead is

`p₀(b) = [b²+(b−1)²]/2 = b²−b+1/2 = (b−1/2)²+1/4`.

Formal utility of true type `0` is `−1/2`, versus `−1/4` from report `1/2`; the formal definition rejects both BIC and interim IR. Neither direction can be salvaged by a null-event or report-domain objection: the rejecting true type `0` has probability `1/2`, and the deviation `1/2` is an allowed real report.

**Correction:** either require mutually independent types for the existing marginal bidder-problem/BIC/IR interpretation, or introduce two-argument quantities `q_i(s,b)` and `p_i(s,b)` using the opponent kernel conditional on true type `s`. Define `U_i(s)=s q_i(s,s)−p_i(s,s)` and compare `s q_i(s,b)−p_i(s,b)` to truthful utility with the conditioning argument fixed at `s`. Own report is not the conditioning variable. Retain suitable integrability and explicit conditional-kernel/version conventions. The existing simple envelope theorem should remain in the independent-types part of that API rather than being advertised for unrestricted correlated BIC.

### C2 — Expected revenue averages opponents from the wrong law

Location: `Typeclasses.lean:145–146`, relying on `Basic.lean:107–108,131`. Severity: major numerical semantic defect outside independent types.

Use the same finite probability space, intervals, zero allocations, and zero bidder-1 payment. Set bidder-0 payment `c₀(b,t)=bt`. Actual truthful total revenue is `E[θ₀θ₁]=E[ω²]=1/2`. The definition first computes `p₀(s)=s E[θ₁]=s/2`, then averages `p₀(θ₀)`; its result is `1/4`. Every term is integrable and measurable. This is equivalent to replacing the perfectly correlated pair by independent draws before charging the payment.

The error can also go upward: in C1-B the actual truthful revenue is zero, but the defined expected revenue is `E[p₀(ω)]=1/2` because `p₀(0)=p₀(1)=1/2`. Thus zero defined revenue need not characterize zero actual revenue (C1-A has defined zero but actual `1/2`), and zero actual revenue need not have defined zero revenue (C1-B).

**Correction:** define actual expected revenue directly as `E[∑ᵢ rules.payment i (θ · ω)]`. Prove equality to `E[∑ᵢ p_i(θ_i)]` under independent types with the joint measurability and integrability needed for Fubini, or use genuinely conditional interim payments and the tower property. Symmetric-IPV results already assume independence, so the finite correlation witness does not directly contradict their theorem statements. Generic `expectedRevenue` remains mislabeled under its present assumptions.

### C3 — Atomlessness class ignores every bidder except zero

Location: `Typeclasses.lean:46–48`. Severity: moderate standalone class contract defect; no downstream theorem counterexample claimed.

Take two bidders on `[0,1]` with uniform Lebesgue probability, `θ₀(ω)=ω` and `θ₁(ω)=0`; use zero allocations/transfers and intervals `[0,1]`. The class holds because the law of bidder 0 is uniform and has no atoms. Bidder 1 has law `δ₀`, with mass `1` at `0`, so the standard all-bidder atomlessness property fails. The type maps are measurable, pointwise bounded, and independent (a constant random variable is independent of every random variable). No `HasIdenticalTypes` hypothesis is required by the class. Two bidders are minimal: with one bidder the tested coordinate is the only one.

The reverse implication is valid: if every bidder law is atomless, bidder 0's is atomless. Under equal marginal laws, the formal class also implies all-bidder atomlessness, so this issue is harmless in `IsSymmetricIPV` and in the currently inspected public theorems that require identical types.

**Correction:** change the field to `θ_noAtoms : ∀ i, NoAtoms (Measure.map (A.θ i) ℙ)`. Alternatively require `HasIdenticalTypes A` as a class parameter and name/document it as atomlessness of that common law. The all-bidder version composes better with asymmetric environments.

## Pass 4: verification, rejected alarms, and limits

`correlation_verify.py` independently recomputes polynomial coefficients and finite expectations with exact rational arithmetic; it passes and certifies C1-A's identity for every report, C1-B's polynomial and strict deviation, and C2's `1/2` versus `1/4`. The proof that C1-B admits no profitable conditional deviation uses the exact nonnegativity of a real square, not bounded sampling. C3's verification is measure-theoretic: for each real `x`, the uniform singleton probability is zero, whereas the constant type's singleton at zero has probability one. These are exact analytic witnesses; no local Lean compilation is claimed in this note. Root separately reported independent reconstruction and confirmation of C1, C2, and C3 from the actual source; the root review record governs global headline approval.

Rejected alarms and scope restrictions:

* Positive transfers to bidders, negative payment: consistent throughout the inspected code.
* No feasibility bundled into `Auction`: explicitly stated generic mechanism design; separate allocation classes exist.
* No bound containment bundled into `Auction`: explicitly separated and supplied by `HasBoundedTypes` where needed.
* Bounds need not be tight essential infimum/supremum: named *declared* endpoints, so no defect.
* Type-report-only BIC: standard direct-mechanism interpretation, not unrestricted bids outside the report domain.
* Common strategy in `toBidderProblem`: intentional symmetric-strategy restriction; the definition does not promise arbitrary asymmetric profiles.
* Pointwise boundedness rather than almost-sure boundedness, smooth bounded `IsSymmetricIPV`, and all-product-profile ex-post IR are stronger explicit modeling conventions rather than unacknowledged false-negative claims.
* Totalized integrals deliberately permit pathological nonintegrable inputs. Under independent uniforms and payment `c₀(b,t)=1/t` for `t>0` (`0` at zero), formal `p₀=0` and interim IR holds, whereas ordinary conditional utility is `−∞`. The basic module discloses totalization; economic use of these predicates therefore additionally requires payment/utility integrability. This is recorded as a contract restriction, separately from C1/C2, whose witnesses have no integrability pathology.

No source edits, dependency installations, or source compilation were performed for these checks.
