# Independent verification of auction and affiliation candidates

Source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`.

The verifier independently read the actual declarations, reconstructed the witnesses, and checked the hypotheses and quantifiers. A separate hostile reviewer read the affiliation source and independently proved those examples. No library source was changed. These are analytic and exact-arithmetic verifications; they are not Lean certificates. The standalone checker is `verification/check_auction_candidates.py`; its saved result is `verification/check_auction_candidates.output.json`.

## Verdict matrix

| Candidate | Verdict | Severity | Precise locations |
| --- | --- | --- | --- |
| Unconditional opponents used as interim beliefs | Accept: both false-positive and false-negative BIC, and false-positive InterimIR | P1 | `Auction/Basic.lean:99–108,127–134,181–194`; bidder adapter `206–213` |
| Expected revenue recomputes opponents independently of own type | Accept; distinct incorrect aggregate built on same cause | P1 | `Auction/Typeclasses.lean:145–146` |
| Atomless-types class checks only bidder 0 | Accept outside symmetric scope; no identified downstream false theorem | P2 | `Auction/Typeclasses.lean:46–48` |
| Signal/value environment admits zero density | Accept at probability-environment interpretation; reject as criticism of deliberately algebraic `Affiliated` | P2 | `Auction/Affiliation/Basic.lean:109–122,157–172` |
| Global regularity forbids ordinary zero-boundary private values | Accept false negative, including any extension outside support | P2 | `Auction/Affiliation/Basic.lean:125–132` |
| Density-version-dependent independence/affiliation | Accept at distribution-level wrappers; reject as defect in the expressly pointwise algebraic predicates | P2 | wrappers `Auction/Affiliation/Basic.lean:154–159`, IPV `168–172`; algebraic scope `43–62` |
| Correlated all-purchase net cost | Accept as duplicate consequence of first finding | No additional count | `Auction/AllPurchase/LinearScarcity.lean:99–106,139–147,239–251` |

P1 means the definition changes incentive or revenue conclusions for an allowed ordinary finite model. P2 means a meaningful concept mismatch whose impact is narrower, qualified by advertised scope, or currently protected by additional downstream assumptions.

## 1. Interim beliefs: two bidders and two positive-probability states

Let `n=2`, `Ω={0,1}`, and `P(0)=P(1)=1/2`. Give both bidders type `θ_i(ω)=ω`, with declared intervals `[0,1]`. They have bounded and identical types. No independence hypothesis appears in `Auction`, `q_strat`, `p_strat`, `BIC`, or `InterimIR`. Use zero allocations at every report profile, zero bidder-1 payment, and bidder-0 payment `c(b,t)`, where `b` is bidder 0's report and `t` is bidder 1's report. Signed transfers are `−c` as required by `Mechanism.payment` (`Mechanism/Core/Mechanism.lean:69–71`). Polynomial payments and constant allocations are measurable; all state integrands are finite sums, hence integrable. The zero allocation is feasible even for one indivisible good.

The standard conditional interim payoff at true type `s` and report `b` uses `P(θ_1 | θ_0=s)`. For this law, at both realized types `s=0,1`, that conditional law is `δ_s`. In contrast, the definitions at `Basic.lean:99–108` average over unconditional `θ_1`, irrespective of the true type. BIC and interim IR require conditional beliefs in the standard formulation; see [Jackson, Mechanism Theory, sections 4.1 and 4.4, printed pp.19 and 22](https://web.stanford.edu/~jacksonm/mechtheo.pdf#page=19).

### 1a. False positive: formal BIC and InterimIR both hold

Take `c(b,t)=(2t−1)b`. For every real report `b`, the formally defined interim payment is

`p_0(b) = [−b+b]/2 = 0`.

Since every formal allocation is zero, every formal utility is zero. Thus every BIC inequality is `0≤0` for **all** `s,b∈[0,1]`, including the interval's nonrealized interior types. Bidder 1's conditions are also `0≤0`. Formal `InterimIR` holds for all types in each stated interval.

At true type 1, the opponent's report is 1 with conditional probability 1. Truthful utility is `−c(1,1)=−1`; reporting 0 gives `−c(0,1)=0`. Therefore truth is not optimal and actual interim IR fails at a type with probability `1/2`. No convention on conditioning at probability-zero types can repair this false positive.

### 1b. False negative: actual truthful reporting is optimal

Take `c(b,t)=(b−t)^2`. At each positive-probability true type `s=0,1`, the actual payoff from every report `b∈[0,1]` is

`u_0(s,b)=−(b−s)^2≤0=u_0(s,s)`.

The sign follows from the square of a real number being nonnegative. This verifies every allowed report, not merely a finite report grid. Bidder 1 is indifferent between all reports. Hence truth is a Bayesian equilibrium and truthful interim utility is zero for every realized type.

If an all-interval conditional specification is required, choose the regular conditional kernel `κ(s)=δ_s` for **every** `s∈[0,1]`. This is measurable: for a Borel set `B`, `s↦κ(s)(B)=1_B(s)`. It is compatible with the diagonal Bernoulli joint law because for Borel `A,B`,

`∫_A κ(s)(B) dP_θ0(s) = [1_A(0)1_B(0)+1_A(1)1_B(1)]/2 = P(θ_0∈A,θ_1∈B)`.

Under this legitimate version, `u_0(s,b)=−(b−s)^2` and the same truthful-optimality proof holds at every `s∈[0,1]`. Thus the witness does not rely on demanding an undefined conditional distribution at null types.

The formal payment instead is

`p_0(b)=[b²+(b−1)²]/2=b²−b+1/2`.

At actual type 0, truth gives formal utility `−1/2`, whereas report `1/2∈[0,1]` gives `−1/4`. The formal BIC inequality fails. Exact polynomial coefficients are checked independently in the script. This direction alone is a BIC false negative; it also illustrates a formal IR failure under the specified conditional kernel, but the main IR defect is already demonstrated unambiguously in 1a.

### Minimality and correction

Two bidders are needed for a correlation between own and opponents' information; two positive-probability states suffice and a one-state prior cannot generate this distinction. Both examples use only polynomial transfers and zero allocations.

A general correlated-types definition needs **two** type/report arguments:

`qCond(i,s,b)=E[x_i(b,θ_−i) | θ_i=s]`,

`pCond(i,s,b)=E[c_i(b,θ_−i) | θ_i=s]`.

BIC must compare `s*qCond(i,s,b)−pCond(i,s,b)` with `s*qCond(i,s,s)−pCond(i,s,s)`. Merely conditioning `q(i,b)` on the report `b` is insufficient: both sides must use the true type's beliefs. Alternatively, retain the existing scalar interim decision problem but require independent types wherever it is called a bidder's interim problem, and scope the incentive and payment-equivalence interpretation accordingly. In particular, a type-independent `BidderProblem.cost` cannot generally encode the correlated model's type-dependent conditional cost.

## 2. Expected revenue is wrong for the same allowed correlated prior

Use the same types, intervals, and zero allocations, but bidder-0 payment `c(b,t)=bt`. Then `p_0(b)=b/2`, bidder-1 payment is zero, and `expectedRevenue` at `Typeclasses.lean:145–146` is

`E[p_0(θ_0)] = E[θ_0/2] = 1/4`.

Actual truthful revenue is

`E[c(θ_0,θ_1)] = E[ω²] = 1/2`.

The event-level evaluation uses the same state for both coordinates, whereas the nested expectation in the formal definition effectively uses separate states. Every payment in this witness is integrable and nonnegative on the stated report box. No BIC assumption is needed by `expectedRevenue`; the example does not assert BIC. The exact values are reproduced in the checker.

Correction: define truthful expected revenue directly as `E[∑ i, A.rules.payment i (A.θ · ω)]`, with integrability conditions for interpreting or manipulating it as an expectation. Prove agreement with the present nested formula under independence and suitable integrability. This is a separately incorrect definition even though its cause is related to finding 1.

## 3. HasAtomlessTypes accepts an atomic bidder

On `Ω=[0,1]` with its uniform probability law, take `n=2`, `θ_0(ω)=ω`, `θ_1(ω)=0`, and bounds `[0,1]` for both. Use any constant measurable allocation and zero transfers to complete `Auction`.

For every real `a`, the singleton `{a}` has zero Lebesgue measure, so `P(θ_0=a)=0`; thus the required `NoAtoms(map θ_0 P)` field exists. For bidder 1, `P(θ_1=0)=P(Ω)=1`, so `map θ_1 P=δ_0` is not atomless. Even independent types do not repair the mismatch: a constant variable is independent of the other variable. Two bidders are minimal because with one bidder the checked coordinate is the entire family.

The class therefore is weaker than all bidders having atomless type distributions. The reverse implication does hold: if all bidders' distributions are atomless, then bidder 0's is atomless. Existing uses inspected in `SymmetricIPV`, `StrictMonotonicity`, and all-purchase revenue also assume identical distributions, which lets atomlessness transfer to every bidder. No false theorem in those protected uses is asserted.

Correction: make the field `θ_noAtoms : ∀ i, NoAtoms (Measure.map (A.θ i) P)`. Alternatively require `HasIdenticalTypes A` in this class and describe it explicitly as atomlessness of the common distribution. The universal field preserves the composable nonsymmetric interpretation advertised by the typeclass family.

## 4. SignalValueEnv admits a zero probability density

Take `n=1`, `x_lo=0`, `x_hi=1`, `f(X)=0`, and `v_0(X)=exp(X_0)`. Nonnegativity and support of `f` hold at every profile. Exponential is nonnegative, continuous, increasing, and strictly increasing in its own real argument. Thus every field at `Affiliation/Basic.lean:109–132` holds. Values depend only on own signal. With `g_0≡0`, the one-factor product is zero, so `HasIndependentSignals` and consequently `IsIPV` both hold; `HasAffiliatedSignals` also holds because both products in its inequality are zero.

But `∫ f=0`, so this `f` is not a probability density. One bidder is sufficient. The witness attacks the claim that the environment carries a joint probability density (`116–117`), not the documented algebraic predicates or the finite weighted-sum lemmas. `Affiliated` explicitly states at `51–52` that genuine-density conditions are separate, and `FiniteCondExp.lean` deliberately allows unnormalized weights; those algebraic choices are not defects by themselves. No existing normalization field or probability measure connecting `SignalValueEnv.f` to signals appears in this structure.

Correction: either add measurable density and total mass one conditions to the probability environment, or name the current object an unnormalized kernel/value environment and introduce a separate probability-environment extension. For a real-valued nonnegative density, a suitable formulation uses measurability plus `∫⁻ X, ENNReal.ofReal(f X) = 1`. The present `f_nonneg` and compact support alone do not imply either measurability or normalization.

## 5. Global value regularity excludes canonical private values on the declared support

Let the intended signal be uniform on `[0,1]`, with value `v_0(X)=X_0` on that support. This is a nonnegative continuous strictly increasing private value on the entire supported interval, with the ordinary uniform density. One bidder already exposes the mismatch; two independent copies give the usual IPV example.

The structure requires global nonnegativity and global strict own monotonicity, even at signals outside its bounds (`Basic.lean:125–132`). Suppose **any** extension `V` matches this on-support value. Then `V(0)=0`, but strict monotonicity at `−1<0` forces `V(−1)<V(0)=0`, contradicting global nonnegativity. This is not merely a poor choice of off-support values: no extension matching the canonical zero boundary value exists.

More generally, for every admitted `i,X`, put `X⁻=update X i (X_i−1)`. Strict own monotonicity and the update identities give `v_i(X⁻)<v_i(X)`. Global nonnegativity gives `0≤v_i(X⁻)`, so every admitted value is strictly positive at every profile. Therefore all otherwise valid zero-valued boundary types are excluded, even though the source advertises nonnegative values.

Correction: restrict nonnegativity and the value regularity hypotheses to `box={X | ∀ i, X_i∈[x_lo,x_hi]}`. Use `ContinuousOn`, `MonotoneOn`, and own-signal `StrictMonoOn` for admissible rival profiles and own arguments in `[x_lo,x_hi]`. If global regularity is intentional, explicitly advertise strictly positive global values as an additional modeling restriction; it is stronger than the claimed support-based concept.

There is a second verified consequence of the same global-domain mismatch at `IsPrivateValues` (`137–138`). Take two independent uniform signals on `[0,1]`, its normalized square density, and global maps

`v_0(X)=exp(X_0)+max(0,X_1−1)`, `v_1(X)=exp(X_1)`.

They satisfy every value field: the positive part is continuous, nonnegative, and nondecreasing; the own-coordinate dependence is exponential and strictly increasing for each bidder. On **every** supported profile, `X_1≤1`, so the extra term is zero and values depend only on own signal. Nevertheless, the global `IsPrivateValues` is false: `X=(0,1)` and `Y=(0,2)` have the same own coordinate for bidder 0, but values 1 and 2. Both values are checked exactly using `exp(0)=1`. Two bidders are minimal for such rival-signal dependence. Restrict the private-values quantifiers to supported profiles as part of the same domain correction. This is a subsidiary false negative, not an additional top-level finding.

## 6. Distribution-level dependence wrappers distinguish equal density versions

Use `n=2`, bounds `[0,1]`, the independent-uniform law on the unit square, and values `v_i(X)=exp(X_i)`. Both coordinates' values satisfy every global field. Let `h(X)=1_[0,1]²(X)`. For `a=(0,0)` or `(0,1)`, define `f_a(a)=2` and `f_a(X)=h(X)` elsewhere.

Each `f_a` is measurable and nonnegative, supported on the declared box, and has integral one: a singleton is measurable and has two-dimensional Lebesgue measure zero, so its finite modification changes no integral over any measurable set. Therefore **all three** densities `h,f_(0,0),f_(0,1)` represent precisely the same independent-uniform probability law. This remains a counterexample after adding the missing probability-density conditions from finding 4.

### 6a. Origin spike defeats pointwise independence

Suppose `f_(0,0)(x,y)=g_0(x)g_1(y)` everywhere, as required by `Factors`. Multiplying the equations at `(0,0)` and `(1,1)` yields the same four factors as multiplying those at `(0,1)` and `(1,0)`. Therefore every factorization must satisfy the corner identity

`f(0,0)f(1,1)=f(0,1)f(1,0)`.

For the origin spike, this is `2·1=1·1`, a contradiction. The argument allows arbitrary real factors and assumes no unmentioned regularity. Hence `HasIndependentSignals` rejects an independent law. The exact determinant `2−1=1` is checked in the script.

This particular density **remains pointwise affiliated**. If one profile is outside the cube, its right-hand product is zero and the left is nonnegative. If both profiles are in the cube, their join and meet also are. If neither right-hand factor is at the origin, the right product is 1 and the left product is at least 1. If one right-hand factor is at the origin, the two profiles are comparable in the nonnegative cube and the lattice products agree. This separates independence failure from affiliation failure.

### 6b. Off-diagonal spike defeats pointwise affiliation as well

For `f_(0,1)`, choose `x=(0,1)` and `y=(1,0)`. Then `x∨y=(1,1)` and `x∧y=(0,0)`. The required affiliation inequality is

`1·1 ≥ 2·1`,

which is false. The same corner identity also forbids factorization. The independent-uniform distribution itself is affiliated, as certified by its ordinary product density `h`; changing one singleton does not change it.

Two coordinates are minimal: with one coordinate every function factors as itself, and every pair of arguments is comparable, so the lattice-product equality is automatic. Four corner evaluations suffice to certify each obstruction.

An equally explicit variant changes only the **interior** point `a=(1/2,1/2)` to density 2. Product factorization fails on the rectangle with coordinates `{1/2,1}`, where the diagonal products are 2 and 1. For affiliation use `x=(1/2,1/2)`, `y=(1,0)`, whose join is `(1,1/2)` and meet `(1/2,0)`; again the left product is 1 and the right product is 2. The checker verifies this alternative too. It avoids any dependence on how densities are conventionally displayed at support endpoints.

### Scope and correction

`Factors` (`58–62`) and `Affiliated` (`43–54`) are correct **pointwise algebraic** predicates. In particular, do not report that the algebraic lemma `factors_affiliated` is false. The semantic mismatch occurs in the wrappers `HasIndependentSignals` (`157–159`) and `HasAffiliatedSignals` (`154–155`) and the probabilistic interpretation of `IsIPV` (`168–172`): they are not equivalent to properties of the represented probability distribution without a representative convention. No continuity or canonical-version assumption on `f` repairs that omission in the current structure.

Milgrom and Weber's original distribution-level formulation is version invariant; [Appendix Theorem 24, printed p.1119](https://ranger.uta.edu/~weems/NOTES6319/PAPERSTWO/milgrom.pdf#page=31) states its density characterization using a Lebesgue-almost-everywhere inequality. This supports treating the present wrapper mismatch as a qualified P2 finding, while retaining the algebraic layer unchanged.

Correction: introduce law-level independence through product probability measures or almost-everywhere factorization by marginal densities; introduce law-level affiliation through a version-invariant condition or an appropriate affiliated density representative. Retain the present predicates with explicit names/comments indicating they concern the chosen representative, and prove the bridge under stated probability and representative hypotheses.

## 7. All-purchase net cost: verified duplicate consequence

With the diagonal Bernoulli law from finding 1, take `β=id`, `p=1`, and `φ(B)=2−B`. Use the all-purchase rules: bidder `i` wins only if strictly highest, and net payment is `(1−φ(b_i+b_j))*b_i`. The price is positive, `φ` is continuous and strictly decreasing, and the linear-scarcity fields are satisfied by `φ_bar=2`, `α=1`. The strict highest allocation indicator is Borel measurable. Types are identical, and every strategy value is integrable on the two-state space. All hypotheses of the displayed quadratic-cost construction hold; no independence is required there.

At bid `b=1`, the all-purchase net payment against opponent report `t` is `t`. Consequently its formal expected net cost is `E[t]=1/2`. At actual own type 1, the opponent is certainly type 1 and purchases 1, so conditional net cost is 1. The formal winning probability is `P(t<1)=1/2`, whereas actual conditional winning probability is 0 because the bids tie. Formal utility is `1·1/2−1/2=0`; actual utility is `1·0−1=−1`. The independent exact checker computes all four quantities.

The algebraic expected-scarcity and quadratic identities are valid for their explicitly unconditional averages. The error is interpreting the type-independent scalar object as the bidder's interim decision problem (`LinearScarcity.lean:239–251`). Count this under finding 1 rather than as an additional defect. Under general correlation, the conditional linear term is `K_i(s)=p−φ_bar+α∑_(j≠i)E[β(θ_j)|θ_i=s]`; it depends on the true type. Impose independent types for the scalar adapter or use a conditional, type-dependent cost problem.

## Verification limits

The checker uses `fractions.Fraction` only, independently conditions the finite diagonal prior by selecting positive-mass cells, verifies polynomial coefficient identities exactly, and verifies all decisive deviations, revenues, corner determinants, and all-purchase costs. Its report grid is a supplemental sanity check; the continuum claims are proved algebraically above. Atomlessness, null-set equivalence, exponential regularity, and the zero-boundary obstruction are analytic arguments. No claim of a completed Lean build or general result inferred from bounded computation is made.
