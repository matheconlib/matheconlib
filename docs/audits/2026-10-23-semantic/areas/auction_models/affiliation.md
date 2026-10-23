> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Affiliation definitions semantic audit

Scope: `MathEconLib/Auction/Affiliation/{Basic,LogSupermodular,FiniteCondExp,MonotoneCondExp,WinnersCurse}.lean` as read on 2026-10-23. Read-only audit: no library source changed. Every inventoried entry is mapped below. There are three substantive finding groups, with explicit qualifications separating algebraic definitions from probabilistic interpretations.

## Findings

### AFF-1 — Global value restrictions exclude bounded-signal models (major false negative)

**Locations:** `Basic.lean:109–132`, especially `v_nonneg` at126 and `v_strictMono_own` at132; `IsPrivateValues` at137–138 is affected by the same domain mismatch. The declared signal domain is the bounded box (110–122), but every value restriction quantifies over all real profiles.

**Intended concept:** continuous nonnegative values on the signal domain, weakly increasing in all signals and strictly increasing in the bidder's own signal. The standard private-values example is `v_i(X)=X_i` with signals in `[0,1]`. Milgrom–Weber explicitly identifies `V_i=X_i` as its private-values special case (printed1098; see primary source below).

**Minimal witness:** one bidder, uniform signal on `[0,1]`, value `v(X)=X_0`. The value is continuous, nonnegative, and strictly increasing on its declared signal domain. The formal environment cannot represent this example, **even using any extension outside the signal box** that agrees with these values on `[0,1]`.

**Exact impossibility proof:** for any formal environment, bidder `i`, and profile `X`, put `Y=Function.update X i (X i−1)`. Global own strict monotonicity gives `v_i(Y)<v_i(X)` and global nonnegativity gives `0≤v_i(Y)`. Thus every formal value satisfies `0<v_i(X)` everywhere. At the all-zero profile, agreement with the example instead requires `v_i(X)=0`, a contradiction. This argument works for any positive bidder count and does not concern the density's normalization.

**Additional independently checked witness for private-values classification:** two independent uniform signals on `[0,1]^2`; set `v_0(X)=exp(X_0)+max(0,X_1−1)` and `v_1(X)=exp(X_1)`. Both value maps are globally continuous, nonnegative, product-monotone, and strictly increasing in their own coordinate, so this witness is compatible with every formal value field. On the entire declared signal box the maximum term is zero, so both values depend only on own signals. Nevertheless `v_0(0,1)=1` and `v_0(0,2)=2` have identical own signal, disproving formal `IsPrivateValues`. Economic private-values status is therefore sensitive to an entirely off-support extension.

**Both directions:** formal value regularity implies the intended box regularity; the converse fails as above. Formal `IsPrivateValues` implies private values on the box, but the converse fails in the second witness.

**Proposed correction:** define profiles as `Fin n → Set.Icc x_lo x_hi`, or restrict every field to the declared box: nonnegativity there, `ContinuousOn`, `MonotoneOn`, and own-coordinate `StrictMonoOn ... (Set.Icc x_lo x_hi)` with rivals valid. Restrict `IsPrivateValues` to valid profiles as well. This preserves all intended on-support comparisons and admits the canonical endpoint-zero example.

**Independent verification:** an independent reviewer rederived the strict-positivity consequence and checked every field of the second witness. Exact arithmetic checks verify the displayed values1 and2. Optional LeanProbe proof checking timed out during server startup; no formal certificate is claimed.

### AFF-2 — The environment does not require a probability density (false positive; packaging scope)

**Locations:** `Basic.lean:116–122` calls `f` a joint density but requires only pointwise nonnegativity and zero off the box; probabilistic names at155,159,172 inherit the omission.

**Minimal witness:** one bidder; `x_lo=0`, `x_hi=1`; `f(X)=0` for every profile; `v_0(X)=exp(X_0)`. Bounds are valid, the zero density is nonnegative and supported on the box, and the exponential value is globally positive, continuous, monotone, and strictly increasing in own signal. Thus every structure field is satisfied. The environment is `IsPrivateValues`; choosing the sole factor `g_0(t)=0` gives `HasIndependentSignals`, hence `IsIPV` and `HasAffiliatedSignals`.

**Failure:** `∫f=0`, whereas a probability density must have integral1. No probability distribution with density `f` exists. Consequently these predicates do not by themselves assert that any random signals exist. Measurability is also absent, but the zero function suffices without any pathological example.

**Both directions:** a genuine probability density satisfying the stated pointwise support properties supplies the formal `f` fields; formal fields fail to imply a genuine density. There is no corresponding density-specific false negative here beyond pointwise support/version issues discussed separately.

**Proposed correction:** retain the useful algebraic/unnormalized layer and add a probabilistic wrapper carrying a base measure, measurability, and unit total mass (or a nonzero finite mass plus an explicit normalization operation). Define the probabilistic signal and IPV predicates on that wrapper.

**Scope qualification:** `Affiliated` explicitly says it is an algebraic inequality at51–52; its lack of a density hypothesis is deliberate and correct. The finite conditional-expectation modules explicitly work with unnormalized weights and normalize nonempty positive events; their theorems do not fail on this witness because positivity hypotheses reject `f=0`. This finding is about `SignalValueEnv`'s advertised probability interpretation, not a false algebraic theorem.

**Independent verification:** reviewer checked exponential regularity, zero-factor construction, and mass0 analytically. Finite check script also verifies zero total discrete mass; that discrete calculation is illustrative and is not the proof of the continuous integral claim.

### AFF-3 — Signal predicates depend on null-set choices of density (false negatives)

**Locations:** `HasIndependentSignals` at `Basic.lean:157–159`, `HasAffiliatedSignals` at154–155, and inherited `IsIPV` at168–172. Their subordinate algebraic `Factors` at61–62 and `Affiliated` at53–54 are intentionally pointwise. Once those subordinate predicates are named as properties of random signals, they become stronger than the standard law-level concepts without extra density regularity or a canonical representative.

**Intended concepts:** independence and affiliation of the signal law. Changing a density on a Lebesgue-null set leaves that law unchanged. This issue survives repairing AFF-2: both witnesses below are measurable, nonnegative, supported on `[0,1]^2`, and integrate to1. Take globally private values `v_i(X)=exp(X_i)` to satisfy all other environment fields.

**Independence witness:** let `f=1_[0,1]^2`, except set `f(0,0)=2`. This differs from independent uniform density on one null singleton, so represents exactly the independent uniform law. Every pointwise product `f(x,y)=g_0(x)g_1(y)` satisfies the rectangle identity

`f(0,0) f(1,1) = f(0,1) f(1,0)`.

The displayed density instead gives `2·1=2` and `1·1=1`. Thus **no factors whatsoever** work, and `HasIndependentSignals` is false. Dimension2 is minimal: for one coordinate any function trivially factors. This density is still pointwise affiliated: if either input is outside the box the right product is0; inside the box, a zero-corner input is comparable with every profile and gives equality, while for all other inputs the right product is1 and the left product is1 or2. Thus the witness isolates independence rather than introducing an affiliation failure.

**Affiliation witness:** let `h=1_[0,1]^2`, except `h(c)=2` at `c=(1/2,1/2)`. The law again is independent uniform and therefore affiliated. But with `x=c` and `y=(1,0)`, `x∨y=(1,1/2)` and `x∧y=(1/2,0)`. All three of `y,x∨y,x∧y` have density1, so the formal inequality reads `1≥2`, false. It follows that formal `HasAffiliatedSignals` also rejects a density of an affiliated signal law.

**Both directions:** for genuine probability densities, pointwise nonnegative product factorization is sufficient for independent signals, and pointwise MTP2 is sufficient for affiliated signals. Conversely independent/affiliated laws need not have their **supplied** density representative satisfy the pointwise condition. These examples establish exactly that direction; they do not refute either algebraic definition or either proved sufficient implication.

**Proposed correction:** define signal independence directly through a probability measure (`iIndepFun`/product law), or require almost-everywhere factorization into actual marginal densities. Define signal affiliation via the law, almost-everywhere MTP2, or existence of a suitable density representative. Keep pointwise `Affiliated` and `Factors` as separate sufficient algebraic APIs. Alternatively state and enforce regularity strong enough to identify a canonical representative; no such regularity appears now.

**Independent verification:** reviewer independently checked both null modifications, normalization, all four rectangle values, and the explicit MTP2 violation. Exact `Fraction` computations reproduce both obstructions. The null-set law argument is analytic, not extrapolated from the finite grid.

## Declaration-by-declaration coverage

The final comment-aware inventory has13 definitions/structures here. The earlier inventory's `Basic:162` entry was the prose “structure sits on the boundary…” inside a docstring, not a Lean structure; it was correctly removed before final reconciliation.

| Location | Declaration | Standard concept | Formal ⇒ intended | Intended ⇒ formal / scope |
|---|---|---|---|---|
| Basic:53–54 | `Affiliated` | Pointwise MTP2 / lattice log-supermodularity in multiplicative form | Exact algebraic equivalence | Exact for the explicitly declared algebraic scope; density/law requirements separate. Signed inputs are expressly allowed, so not misreported as density bugs. |
| Basic:61–62 | `Factors` | Pointwise multiplicative separability | Exact algebraic equivalence | Exact algebraically; not equivalent to independence of a supplied density's law, AFF-3. No requirement that the supplied factors themselves be marginal densities. |
| Basic:109–132 | `SignalValueEnv` | Bounded-signal interdependent-values environment | Value restrictions hold on box, but probability interpretation absent, AFF-2 | Fails on endpoint-zero canonical values and off-support restrictions, AFF-1. `x_lo≤x_hi` permits singleton boxes, valid as a box but not a positive-mass Lebesgue density for n>0. |
| Basic:137–138 | `IsPrivateValues` | Values factor through own signal | Yes on valid profiles | Global factorization too strong for economic on-support dependence, AFF-1 subsidiary witness. |
| Basic:142–143 | `SignalValueEnv.value` | Evaluate bidder value at profile | Definitional identity | Exact abbreviation, no independent content. |
| Basic:155 | `HasAffiliatedSignals` | Affiliation of signal law | Sufficient once actual law/density assumptions added | Law⇒pointwise supplied representative fails, AFF-3. Exact if read merely as the declared density-level predicate. |
| Basic:159 | `HasIndependentSignals` | Mutual independence | Sufficient for normalized genuine density | Converse fails for null-modified representative, AFF-3; zero-density false positive absent probability wrapper, AFF-2. |
| Basic:172 | `IsIPV` | Independent private-values environment | Requires probability assumptions and on-support reading | Inherits AFF-1 through AFF-3; conjunction itself is correct. No i.i.d. requirement, which is appropriate for IPV rather than symmetric IPV. |
| FiniteCondExp:45–46 | `condExpOn` | Conditional weighted average on finite event | Exact when weights≥0 and event mass>0 | Same formula; outside that scope it is an explicitly totalized algebraic ratio. Zero denominator convention is documented. |
| MonotoneCondExp:49–51 | `condExpSlice` | Discrete expectation given own signal t | Exact with positive slice mass | Exact formula; empty/nonpositive conditioning cases explicitly outside interpretation and theorem scope. |
| WinnersCurse:53–55 | `ownSignalSlice` | Support event `X_i=t` | Exact | Exact set filter. |
| WinnersCurse:60–62 | `winningSlice` | Own signal t and weak maximum of all signals | Exact for explicit tie-as-win convention | Exact for weak-maximum event; no claim this implements allocation probabilities under a tie-breaking mechanism. |
| WinnersCurse:71–73 | `condExpWinningSlice` | Weighted expectation on weak-maximum own-signal event | Exact when mass positive | Exact formula; zero mass convention documented. |

### Structure field coverage

Bounds110–115 faithfully describe a nonempty closed real interval. Density117–122 supplies a nonnegative supported function but omits probability axioms (AFF-2). The value function124 and its regularity126–132 have correct signs and coordinate roles but wrong domain for the stated bounded-signal concept (AFF-1). No symmetry or common-value requirement is silently inferred: the comments145–150 explicitly leave symmetry to future work, and winner's-curse statements expressly use the more general monotone interdependent-value assumptions.

## Theorem and boundary checks

- `Basic:67`,80,93,163,176: the factorization-to-affiliation proofs are valid algebraic implications. Per-coordinate max/min only permute the two arguments, so no positivity is needed. The resulting law claims require the qualifications above.
- `LogSupermodular:43–62`: exactly the standard log reformulation under its stated **global strict positivity**. Log multiplication and order are licensed. A compactly supported environment's zero-extended density does not satisfy this global-positivity assumption; this limits applicability, not correctness. No equivalence is claimed for zero densities.
- `FiniteCondExp:52`,63,100,226,260: positive finite sums, translation identity, Ahlswede–Daykin cross-product comparison, normalization, and removal of nonnegativity were inspected. Sublattice closure, both event closure conditions, positivity, nonemptiness, and monotonicity have the correct directions. The final theorem shifts by a finite minimum and cancels the same constant; no reversed stochastic order found.
- `MonotoneCondExp:64`: slice at lower t is lattice-lower than slice at higher t; `MonotoneOn` restricts to realized heights. This avoids the totalized zero-value nonmonotonicity at unobserved heights. The theorem is explicitly finite; no continuous conditional-expectation claim is proved.
- `WinnersCurse:79,86,92,98,106,117,133`: filters, inclusion directions, and meet/join membership faithfully implement their documented events. At fixed own signal t the winning event is lower in the rival coordinates.
- `WinnersCurse:159,194,247`: the finite comparison gives the correct weak direction `winning≤own-only`. Ties count as wins by express definition; strict generic curse and actual tie-breaking are not claimed. The last environment theorem samples `E.f` as finite weights; it should be interpreted for that finite measure, not as the integral conditional expectation of an arbitrary continuous law.

Exact exploratory regression evidence: all81 weight vectors on the four-point binary square with entries1,2,3 were inspected;48 are affiliated. All20 monotone functions with range contained in `{−1,0,1}` were used. Own-signal monotonicity and winning-slice inequalities passed5760 exact rational comparisons. This evidence is restricted to the enumerated grids; it does not prove the general theorems or establish independence of the continuous witnesses.

## Sources and verification boundary

Primary mathematical source: [Milgrom and Weber, A Theory of Auctions and Competitive Bidding (1982)](https://ranger.uta.edu/~weems/NOTES6319/PAPERSTWO/milgrom.pdf). Printed1098 supplies the canonical private-values specialization and density-level affiliation inequality; printed1119, Theorem24, explicitly connects law affiliation to an almost-everywhere density inequality. These narrow source uses support the concept identification and law/version distinction; the counterexamples and calculations above are independent arguments.

All four passes completed: declaration inventory and concept map; search in both directions; explicit witnesses; adversarial review by independent `verify_basic_candidates` agent. The independent review agreed with all displayed witnesses and specifically warned against attributing AFF-2 to the explicitly algebraic `Affiliated` definition. No alleged Lean-kernel inconsistency, no source mutation, and no full project build are claimed. LeanProbe timed out (`success=false`, error `timeout`); evidence records that limitation rather than treating it as acceptance.

Reproducible evidence files: `affiliation-evidence/check_finite.py`, its JSON output, and `verification-status.json`. The timed-out optional Lean candidate was removed from the deliverable; no certification is inferred from that attempt. Root-level independent Lean verification is recorded separately in the consolidated audit.
