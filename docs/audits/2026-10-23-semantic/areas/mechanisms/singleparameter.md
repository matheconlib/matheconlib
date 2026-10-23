> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# SingleParameter semantic audit

Audit date: 2026-10-23. Scope: all six files under `MathEconLib/SingleParameter/`.

## Result

No substantive semantic defect established in these files. All 17 major declarations below match their explicitly documented specialization. The distinction between an arbitrary action and an in-interval report is handled correctly in the revelation construction. Empty/reversed type intervals and zero outside-option normalization are explicitly documented, rather than hidden assumptions.

This is a source-level semantic assessment, not a claim that the entire project builds.

## Definition inventory and equivalence assessment

| Source | Declaration | Standard concept and assessment |
|---|---|---|
| `MathEconLib/SingleParameter/Basic.lean:53` | `SingleParameterProblem` | One-agent, one-dimensional quasilinear choice problem, bundled with a strategy; allocation is an expected quantity/probability in `[0,1]`, payment is signed. Correct for the documented unit-demand, risk-neutral specialization. It intentionally excludes non-affine type-action payoffs and does not assert feasibility relative to another agent. |
| `MathEconLib/SingleParameter/Basic.lean:72` | `typeInterval` | Closed interval of admissible valuations. Exactly `Icc lowestType highestType`. Empty intervals are explicitly allowed. |
| `MathEconLib/SingleParameter/Basic.lean:79` | `payoff` | Quasilinear expected surplus `v q(a) - p(a)`. Exactly the stated signed-payment convention. |
| `MathEconLib/SingleParameter/Basic.lean:83` | `q` | Allocation induced by the bundled strategy. Exact composition with `strategy`. |
| `MathEconLib/SingleParameter/Basic.lean:87` | `U` | Indirect/on-strategy utility. Exact payoff at the selected action; optimality is separately imposed by an IC predicate. |
| `MathEconLib/SingleParameter/Basic.lean:119` | `withStrategy` | Change the behavioral strategy, holding the mechanism primitives fixed. Correct; it makes no claim to preserve IC. |
| `MathEconLib/SingleParameter/Basic.lean:136` | `reduce` | Direct revelation mechanism obtained by composing the original outcome/payment rules with a strategy. Correct. Its formal action space is all reals; the revelation IC theorem correctly limits feasible reports to the original interval. |
| `MathEconLib/SingleParameter/IC.lean:55` | `HasEnvelopeIC` | Global subgradient/supporting-hyperplane inequalities for indirect utility. Exactly equivalent to the next type-deviation predicate under the defined quasilinear utility (see algebra below). It is stronger than an a.e. envelope identity without monotonicity. |
| `MathEconLib/SingleParameter/IC.lean:62` | `HasTypeDeviationIC` | No profitable deviation to an action assigned to another admissible type. Exact pairwise incentive inequalities. Correctly makes no claim about unused actions. |
| `MathEconLib/SingleParameter/IC.lean:71` | `HasUniversalIC` | Optimal strategy against every action in a specified feasible set. Both optimality and feasibility of the selected strategy action are required. Exactly this concept; `S` need not be all actions. |
| `MathEconLib/SingleParameter/IC.lean:149` | `IsIndividuallyRational` | Ex post one-agent participation with outside utility normalized to zero. Exact nonnegativity for every admissible type. |
| `MathEconLib/SingleParameter/IC.lean:157` | `HasZeroLowestTypeUtility` | Binding bottom-type participation normalization. Exact equality, explicitly stronger than bottom-type IR. |
| `MathEconLib/SingleParameter/Revelation.lean:65` | `HasIdentityStrategy` | The total real-valued strategy equals the identity. Exactly the documented global strategy property; this is not merely an IC predicate. |
| `MathEconLib/SingleParameter/PostedPrice.lean:42` | `PurchaseDecision` | Binary purchase/decline action space. Exact. |
| `MathEconLib/SingleParameter/PostedPrice.lean:52` | `PurchaseDecision.allocation` | Unit allocation on purchase, zero on decline. Exact deterministic allocation. |
| `MathEconLib/SingleParameter/PostedPrice.lean:57` | `PurchaseDecision.payment` | Pay the posted price on purchase and nothing on decline. Exact; real prices permit subsidies explicitly. |
| `MathEconLib/SingleParameter/PostedPrice.lean:73` | `postedPriceProblem` | A take-it-or-leave-it offer with purchase at weakly positive surplus. Correct for arbitrary real prices and valuations. Purchase on the zero-surplus tie is an explicitly documented optimal selection. |

## Bidirectional and adversarial checks

1. **Envelope IC versus deviation IC.** Write `q_v = allocation(strategy v)` and `p_v = payment(strategy v)`. The envelope inequality is

   `(v-w) q_w ≤ (v q_v-p_v) - (w q_w-p_w)`.

   Adding `w q_w-p_w` to both sides and collecting coefficients gives

   `v q_w-p_w ≤ v q_v-p_v`,

   exactly the type-deviation inequality. Reversing the algebra gives the converse. This uses no sign, nonempty-interval, regularity, or allocation-bounds assumptions. A second check subtracts the two inequalities' left-minus-right residuals; the difference is identically zero after distributing multiplication. Consequently there can be neither a false positive nor a false negative between these two predicates.

2. **Unused actions are correctly excluded from reduction.** Consider two actions `a,b`, types `[0,1]`, both allocations zero, payments `p(a)=0`, `p(b)=-1`, and strategy constantly `a`. Pairwise/type-deviation IC and envelope IC hold: every comparison is `0≤0`. Universal IC over `{a,b}` fails: every type obtains utility `1` from `b`, but `0` from its prescribed action. The reduced mechanism has constant allocation/payment zero and is universally IC over reports `[0,1]`. Independently checking the primitives: `v·0-0=0`, `v·0-(-1)=1`; the reduction composes only with `a`. This is a separation example validating the source's explicit restriction, not a defect.

3. **Posted price, all signs and the tie.** If `v≥p`, purchase gives `v-p≥0`, dominating decline's zero. If `v<p`, purchase gives a strictly negative number and decline gives zero. At `v=p` both give zero. These cases exhaust all real prices/types, so allowing negative valuations/prices is not a counterexample.

4. **Analytic/payment theorems.** `EnvelopeIC.lean:47,63,111,137,167` correctly restrict Lipschitzness, monotonicity, a.e. differentiability, integral representation, and participation to the type interval. Full derivatives need only hold a.e.; the two endpoints are measure-zero. `Payment.lean:47,59,86` uses the same on-strategy quantities, includes the utility integration constant, and requires allocation monotonicity for sufficiency. No missing normalization or payment-sign reversal found.

5. **Revelation theorem.** `Revelation.lean:119` preserves on-strategy allocation, payment, and utility and establishes direct IC only over in-interval reports. It does not incorrectly infer optimality against the original unused actions, or against out-of-interval real reports.

## Optional clarification, not a substantive defect

`MathEconLib/SingleParameter/IC.lean:14–28,49–57` describes three ordered IC levels. The first two are equivalent here, so the sharper description is

`HasUniversalIC P S → (HasTypeDeviationIC P ↔ HasEnvelopeIC P)`.

The displayed one-way implication is true and no false-positive/false-negative counterexample exists. An optional correction is to state this equivalence and provide an explicit reverse theorem (rather than adding a reverse instance and creating an instance-search cycle).

## Verification record

The counterexample in item 2 was checked directly in its allocation/payment primitives and independently after composing the reduced mechanism. No unverified suspected defect is reported. A LeanProbe check of the reverse IC implication was attempted separately and returned `success=false`, `error_code=timeout` after 90 seconds; it supplies no kernel-verification evidence. The worktree initially lacked the relevant project and mathlib build artifacts, so the source/algebraic checks above do not depend on that tool's availability.
