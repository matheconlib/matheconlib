> Published preservation of the 23 October 2026 audit at `1d9f8cc233cdaeee0364b51befb84feea657a4da`. Start with [README.md](README.md) for reproducible commands and proof limits. Original independent verification used separate automated workstreams, not maintainer approval.

# MathEconLib semantic audit

Audited revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`. Date: 23 October 2026.

**Six substantive semantic mismatches were confirmed: two major incentive/revenue errors and four narrower modeling/representation errors.** Every reported counterexample received a separate adversarial verification, followed by the integrating auditor's own source and calculation checks. The all-purchase manifestation is counted with its underlying interim-belief defect.

The audit covers **430 definition-like declarations across 128 library source modules**. Major definitions are mapped to their intended mathematical/economic concepts in the area notes below; helper constructions are grouped with those concepts. Both implication directions and necessary interpretation conditions are assessed. Eight import-only modules introduce no additional concepts. The root umbrella was also checked. Examples and regression tests were consulted as supporting context; this is an audit of the library, not a separate exhaustive audit of example prose.

The library source was left unchanged. These findings concern the meanings of accepted formal statements; no Lean-kernel inconsistency is alleged.

## Findings at a glance

| ID | Priority | Mismatch | Direction | Source |
|---|---|---|---|---|
| F1 | Major | Marginal opponent beliefs presented as conditional interim beliefs | False positives and false negatives for BIC and interim IR | `Auction/Basic.lean:99–108,128–134,181–194,206–213` |
| F2 | Major | Expected revenue resamples opponents rather than charging the actual joint profile | Incorrect value, in either direction | `Auction/Typeclasses.lean:145–146` |
| F3 | Moderate | Atomless-types class tests only bidder zero | False positive | `Auction/Typeclasses.lean:46–48` |
| F4 | Moderate | Signal/value probability environment admits a zero density | False positive for its advertised probabilistic interpretation | `Auction/Affiliation/Basic.lean:109–122,155–172` |
| F5 | Moderate | Bounded-signal value and private-value conditions constrain impossible/off-support profiles | False negatives | `Auction/Affiliation/Basic.lean:125–138` |
| F6 | Moderate, qualified | Signal independence and affiliation depend on the supplied density's null-set values | False negatives relative to distribution-level concepts | `Auction/Affiliation/Basic.lean:154–159,168–172` |

“Major” means that an ordinary allowed finite model changes incentive or revenue conclusions. “Moderate” indicates a substantive but narrower mismatch, including cases protected by extra assumptions in current downstream consumers. F4 and F6 are specifically about probability-environment interpretations; the explicitly algebraic predicates remain correct within their documented scope.

## F1. BIC and interim IR use the wrong beliefs for correlated types

**Exact locations:** [marginal allocation](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Basic.lean#L99), [marginal payment](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Basic.lean#L107), [truthful utility](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Basic.lean#L134), [InterimIR](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Basic.lean#L181), [BIC](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Basic.lean#L192), and [bidder-problem adapter](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Basic.lean#L206).

**Intended concept.** After learning own type, a bidder evaluates every report against the opponents' distribution conditional on that same true type. The formal `q_strat` and `p_strat` instead integrate the unconditional opponent variables. Neither their definitions nor `BIC`/`InterimIR` requires independence. This distinction is standard in the correlated-type formulation; see [Jackson, Mechanism Theory, §§4.1 and 4.4](https://web.stanford.edu/~jacksonm/mechtheo.pdf) and [Bergemann's correlated-types lectures](https://campuspress.yale.edu/dirkbergemann/files/2012/01/lecture2yale2012.pdf).

**Minimal common setup.** Two bidders, two states `ω=0,1`, each with probability `1/2`, and `θ₀(ω)=θ₁(ω)=ω`. Both declared type/report intervals are `[0,1]`. Both allocations are identically zero, bidder 1 pays zero, and bidder 0 pays `c(b,t)`, where `b` is own report and `t` the opponent report. The signed transfer is `−c`, as the library requires. Allocation is feasible and measurable; all state integrands are finite and integrable. Two bidders and two nondegenerate states are minimal for this own/opponent correlation issue.

**False positive:** set `c(b,t)=(2t−1)b`. For every real report,

`p₀(b)=[−b+b]/2=0`, `q₀(b)=0`, and `U₀(s)=0`.

Every formal BIC inequality is `0≤0`; formal interim IR also holds for every declared type. In fact, own type `1` reveals opponent type `1`. Truth gives utility `−1`; reporting `0` gives `0`. Both economic BIC and interim IR fail at a positive-probability type.

**False negative:** set `c(b,t)=(b−t)²`. Given true type `s=0` or `1`, actual utility from **every** report `b∈[0,1]` is

`−(b−s)²≤0`, with equality from truthful reporting.

Thus the mechanism is genuinely BIC and interim IR. If incentives are to be specified even at unrealized interior types, the measurable conditional kernel `κ(s)=δ_s` is a valid version on the whole interval and yields the same conclusion everywhere. Its compatibility with the finite joint prior is proved in the independent verification note.

The formal payment is instead `p₀(b)=b²−b+1/2`. At actual type `0`, formal truthful utility is `−1/2`, versus `−1/4` from report `1/2`. Formal BIC and interim IR both reject this mechanism. This is not a grid-based best-response argument: the truthful-optimality claim holds for all real reports by nonnegativity of a square.

**Accepted correction.** Keep BIC broad: compare reports using beliefs conditional on the **true** type, holding that type and its beliefs fixed during the deviation. The mechanism interface in #210 is explicitly the quasilinear specialization, allowing correlated and interdependent values. Its IPV specialization supplies the independent fixed-menu bridge for scalar envelope/payment results. Independence and quasilinearity are not constitutive of BIC as an economic concept. Conditioning on the reported type remains incorrect. See [the migration record](MIGRATION.md).

**Additional affected construction:** `Auction/AllPurchase/LinearScarcity.lean:99–106,139–147,239–251`. In the same diagonal prior, with `β=id`, price `p=1`, and scarcity `φ(B)=2−B`, bid `1` has formal net cost `1/2` and win probability `1/2`; conditional on own type `1`, its actual cost is `1` and win probability `0`. The quadratic identities remain valid as unconditional identities; the generic interim bidder interpretation fails. This is a consequence of F1, not an additional finding.

**Verification:** independent source reconstruction, exact polynomial-coefficient/conditional-cell checks, and separate analytic proofs. The real identities and all-report square inequality also compile in [Counterexamples.lean](../../../MathEconLibTest/Audit/SemanticCounterexamples.lean). This formal file proves the algebra, not a fully instantiated finite `Auction.BIC` countermodel; the full economic/formal correspondence is explicitly derived above and in [the independent note](verification/auction-candidates.md).

## F2. `expectedRevenue` need not equal expected receipts

**Exact location:** [Typeclasses.lean:145–146](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Typeclasses.lean#L145), using the marginal payment at `Basic.lean:107–108,131`.

**Intended concept:** expected total payment made at the actual truthful joint type profile. The definition is instead `E[Σᵢ pᵢ(θᵢ)]`, where `pᵢ` has already averaged unconditional opponents.

**Minimal witness:** use F1's two-state setup and `c(b,t)=bt`. Actual revenue is `E[ω²]=1/2`. Formal `p₀(b)=b/2`, hence `expectedRevenue=E[ω/2]=1/4`. All payments are finite and nonnegative on the report box. No BIC premise is required by this definition. Overcounting is possible too: F1's squared-loss payment gives actual truthful revenue zero and formal revenue `1/2`.

**Correction:** define `E[Σᵢ rules.payment i (θ · ω)]` directly. Prove equality to iterated interim payments using genuinely conditional quantities and the tower property, or independence and the integrability needed for Fubini. Symmetric-IPV revenue-equivalence results already require independence; this example does not contradict their protected statements.

**Verification:** two independently written exact-arithmetic reconstructions agree on `1/2` versus `1/4`; root reran both. The displayed real arithmetic also compiles in the formal evidence file.

## F3. `HasAtomlessTypes` ignores all bidders except zero

**Exact location:** [Typeclasses.lean:46–48](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Typeclasses.lean#L46).

**Intended concept:** every bidder's marginal type law has no atoms. The field is only `NoAtoms (map (θ 0) P)` and has no identical-distribution prerequisite.

**Minimal witness:** two bidders, `Ω=[0,1]` with uniform probability, `θ₀(ω)=ω`, and `θ₁(ω)=0`; give both bounds `[0,1]` and zero allocation/transfers. Bidder 0 has no atoms, so the class holds. Bidder 1 has law `δ₀`, with mass one at zero. These types are even independent, since one is constant. With one bidder the mismatch cannot occur. All-bidder atomlessness implies the formal field, so only the reverse direction fails.

**Correction:** use `θ_noAtoms : ∀ i, NoAtoms (map (θ i) P)`. Alternatively require identical types and explicitly identify the class as atomlessness of that common law. Current consumers inspected also assume identical marginal distributions, so no downstream false theorem is claimed.

**Verification:** the independent verifier and integrating auditor separately checked uniform singleton mass zero, constant-law singleton mass one, and the absence of any symmetry premise on the class. This is an exact measure-theoretic witness, not a numerical atom test.

## F4. `SignalValueEnv` can have no signal probability distribution

**Exact locations:** [density fields at Basic.lean:116–122](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Affiliation/Basic.lean#L116); [probabilistic predicates at 155–172](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Affiliation/Basic.lean#L155).

**Intended concept:** a signal/value environment carrying a joint probability density. The structure supplies a nonnegative supported function but neither its measurability nor its unit mass.

**Minimal witness:** one bidder, bounds `[0,1]`, `f≡0`, and `v₀(X)=exp(X₀)`. Every structure field holds: the zero function has the required support and sign, and the value is globally continuous, positive, monotone and strictly increasing in its own coordinate. Private values hold. Taking the sole factor `g₀≡0` proves `HasIndependentSignals`, hence `IsIPV` and `HasAffiliatedSignals`. Nevertheless `∫f=0`, so no probability law has this density.

**Correction:** preserve the algebraic/unnormalized helper layer and add a probabilistic wrapper requiring measurability and total mass one, or nonzero finite mass plus an explicit normalization. Put probabilistic signal predicates on that wrapper.

**Scope:** `Affiliated` expressly defines only an algebraic inequality; its positivity-free formulation is not a defect. Finite conditional-average results expressly normalize unnormalized positive weights and have hypotheses that exclude the zero-event problem. This finding concerns the advertised probability-environment interpretation.

**Verification:** the actual environment, its `IsIPV`/affiliation properties, and its zero mass are constructed and proved in [Counterexamples.lean](../../../MathEconLibTest/Audit/SemanticCounterexamples.lean), successfully compiled against this revision. Two independent analytic reviews also checked every structure field.

## F5. Off-support restrictions exclude ordinary bounded-signal private values

**Exact locations:** [global value requirements at Basic.lean:125–132](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Affiliation/Basic.lean#L125) and [IsPrivateValues at 137–138](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Affiliation/Basic.lean#L137).

**Intended concept:** nonnegative continuous values on the declared signal box, increasing in signals, with private values depending only on own feasible signal. The canonical private-value specialization identifies value with own signal; see [Milgrom–Weber, printed p.1098](https://ranger.uta.edu/~weems/NOTES6319/PAPERSTWO/milgrom.pdf).

**Minimal false negative:** one uniform signal on `[0,1]` with value `v(X)=X₀` on that interval. This satisfies the intended on-support conditions. No globally nonnegative strictly increasing extension can match it: matching at zero forces `v(0)=0`, while strict increase gives `v(−1)<0`. More generally the formal fields force `v_i(X)>0` for every profile, by comparing `X` with the profile whose own coordinate is `X_i−1`. Thus zero-valued boundary types are impossible despite the advertised nonnegativity.

**A separate witness for the private-values predicate:** with two independent uniform signals on `[0,1]²`, let

`v₀(X)=exp(X₀)+max(0,X₁−1)`, `v₁(X)=exp(X₁)`.

All global structure fields hold. On every feasible profile both values depend only on own signal. But the global `IsPrivateValues` predicate compares `(0,1)` and `(0,2)`, giving values `1` and `2` for bidder 0. It rejects economic private values solely because of an off-support extension.

**Correction:** use profiles in `Fin n → Icc x_lo x_hi`, or restrict value hypotheses to the box with `ContinuousOn`, `MonotoneOn`, and own-coordinate `StrictMonoOn`. Restrict `IsPrivateValues` comparisons to feasible profiles too. Formal global regularity does imply the intended on-support regularity; the converse is what fails. Merely choosing different off-support values cannot repair the zero-endpoint example.

**Verification:** the universal strict-positivity obstruction is proved and compiled against the actual structure in [Counterexamples.lean](../../../MathEconLibTest/Audit/SemanticCounterexamples.lean). Independent reviewers also checked the second example's continuity, signs, product monotonicity, strict own monotonicity and displayed values.

## F6. Density versions change allegedly distribution-level signal properties

**Exact locations:** [HasAffiliatedSignals, Basic.lean:154–155](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Affiliation/Basic.lean#L154), [HasIndependentSignals, 157–159](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Affiliation/Basic.lean#L157), and [IsIPV, 168–172](https://github.com/matheconlib/matheconlib/blob/1d9f8cc233cdaeee0364b51befb84feea657a4da/MathEconLib/Auction/Affiliation/Basic.lean#L168).

**Intended concepts:** independence and affiliation of the signal probability law. These are unchanged when a density is modified on a Lebesgue-null set. The wrappers instead impose pointwise factorization/MTP2 on the supplied representative. The standard affiliation characterization is almost everywhere; see [Milgrom–Weber, Appendix Theorem 24, printed p.1119](https://ranger.uta.edu/~weems/NOTES6319/PAPERSTWO/milgrom.pdf#page=31).

**Minimal witness:** two signals on `[0,1]²`. Take its uniform density `h=1_[0,1]²` and change only `f(0,1)` to `2`. Use `v_i(X)=exp(X_i)` so all remaining environment fields hold. A singleton has two-dimensional Lebesgue measure zero, so `f` is measurable, normalized and represents exactly the independent uniform law, which is affiliated.

Yet no pointwise factors exist: every product density satisfies the rectangle identity

`f(0,0)f(1,1)=f(0,1)f(1,0)`,

which here reads `1=2`. Also, at `x=(0,1)` and `y=(1,0)`, pointwise affiliation demands `f(1,1)f(0,0)≥f(0,1)f(1,0)`, or `1≥2`. Both wrappers reject an independent, affiliated law. Dimension two is minimal: in one dimension every function factors and the lattice identity is automatic. This defect survives F4's normalization correction.

**Correction:** define independence on the probability law or through almost-everywhere marginal factorization; define affiliation through the law or existence of a suitable affiliated density representative. Keep pointwise algebraic predicates as explicitly stronger sufficient interfaces and prove the probabilistic bridge. Regularity identifying a canonical density version could support a narrower API, but no such assumption is present now.

**Qualification:** pointwise `Factors` and `Affiliated` are mathematically correct within their expressly algebraic scope. This is a false negative only for their distribution-level wrappers' advertised interpretation. The existence of the ordinary representative `h` does not make the supplied null-modified representative pass the present predicates.

**Verification:** independent hostile reviews rederived the null-set law equality, normalization, rectangle obstruction, and MTP2 violation; exact rational checkers reproduce the four values. The measure argument is analytic and is not inferred from a finite corner grid. A second origin-spike example in the detailed note isolates failure of factorization while retaining pointwise affiliation.

## Coverage of the remaining definitions

The following indexes identify the standard concept and both semantic implications for every inventoried declaration. “No additional confirmed defect” is a review outcome, not a proof that no defect exists.

| Area | Declarations | Source modules | Concept coverage and result |
|---|---:|---:|---|
| Choice | 34 | 10 | [Audit](areas/choice/audit.md): contractive choice, substitutes, IRC, path independence, finite LAD, induced preferences, maps, hulls and completions; no confirmed defect under stated conventions. |
| Contract matching | 40 | 8 | [Audit](areas/contracts/audit.md): bilateral feasibility, individual rationality, blocking/stability, acceptance fixed points, weak substitutes, many-to-one, stable orders, rural hospitals and completion transfers; no confirmed defect. |
| Classical marriage | 81 | 12 | [Audit](areas/marriage/audit.md): strict preferences with outside option, partial matchings, stability/extrema, DA specifications/implementations and contract bridges; no confirmed defect. |
| Strategic games | 50 | 6 | [Audit](areas/strategic/audit.md): best response, dominance, Nash/strong Nash, outcome games, independent mixed actions and existence; no confirmed substantive defect. |
| Bayesian games | 41 | 9 | [Audit](areas/bayesian/audit.md): finite conditional payoffs, positive-marginal BNE, measurable strategies, ex-ante/interim equivalence and action transport; no confirmed defect under explicit conventions. |
| Mechanisms and one-dimensional IC | 51 | 19 | [Audit](areas/mechanisms/audit.md): signed transfers, quasilinear environments, DSIC/IR/budget balance/efficiency, game adapters, menus, reduced/full IC, envelope/payment identities and posted prices; no confirmed substantive defect. |
| Auction core | 28 | 7 | [Audit](areas/auctions/README.md): environments, type classes, interim quantities, BIC/IR, CDF/order-statistic adapters, strict monotonicity and revenue equivalence; F1–F3. |
| Auction models and affiliation | 48 | 12 | [Audit](areas/auction_models/README.md): all-purchase scarcity/cost/revenue/welfare/pricing plus signal models, MTP2, finite conditionals and winner's curse; F4–F6 and F1 consequence. |
| Value distributions and statistics | 17 | 14 | [Audit](areas/pricing/README.md): closed-tail demand, atoms, RN density, virtual value, posted-price accounting/optimality, uniform formulas and order statistics; no confirmed substantive defect. |
| Mathematical foundations and finite probability | 40 | 23 | [Audit](areas/foundations/README.md): partial bijections, orders/iterations, stochastic order, probability kernels/products, finite conditioning/expectations/simplex, approximate selections, uniformization and fixed-point infrastructure; no confirmed substantive definition defect. |
| Import-only modules | 0 | 8 | Checked imports and semantic summaries; no new definitions. |
| **Total** | **430** | **128** | [Machine-readable inventory](inventory.json), [source snapshot](source-snapshot.json), [coverage reconciliation](coverage-results.json). |

The area notes also retain low-priority documentation observations with explicit boundary witnesses and suggested clarifications. Examples include the nonemptiness promise omitted from `exists_star_refinement`'s conclusion and local expected-utility documentation that does not repeat the integrability condition. These are not counted as additional substantive definition errors. Explicit strict-preference, finite-menu, tie-breaking, null-type, pointwise-boundedness and Bochner-totalization conventions were assessed within their stated scope rather than silently broadened.

## Verification and reproduction

The original audit compiled the 128 library modules and root umbrella against the matching
Lean 4.28.0 dependencies. It did **not** run the full default build of tests, examples and API
pins. Initial LeanProbe timeouts supply no acceptance evidence. The new publication branch is
checked separately using the normal full build; its recorded result is in [verification.json](verification.json).

The twelve supporting lemmas are preserved in the canonical test module
[SemanticCounterexamples.lean](../../../MathEconLibTest/Audit/SemanticCounterexamples.lean),
with standard-axiom reports. They formalize the actual zero-density environment and its
properties, the global strict-positivity obstruction, and the decisive real algebra. They do
not formalize every complete auction, continuous signal law, or repaired positive control.
F3 and the null-set/off-support parts of F5/F6 still rely on the explicit mathematical arguments.
The complete F1/F2 regression models belong to #210 and are linked from [MIGRATION.md](MIGRATION.md).

Follow the portable commands in [README.md](README.md). Coverage verification checks frozen
source identities and declaration bookkeeping, not the truth of the semantic assessments.
Finite exact checks certify only the encoded cases; continuum incentive claims require the
stated algebraic argument or the linked Lean proof.

## Repair tracking

[Umbrella #211](https://github.com/matheconlib/matheconlib/issues/211) coordinates F1–F6;
[#218](https://github.com/matheconlib/matheconlib/issues/218) tracks this preservation record.
The [migration table](MIGRATION.md) identifies implementation and closure status separately.
Publishing the evidence does not close the all-purchase follow-up or the other semantic repairs.
