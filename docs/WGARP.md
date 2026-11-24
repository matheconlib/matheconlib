# Finite WGARP rationalization

For a finite dataset with strictly positive prices and nonnegative
observed bundles, WGARP is equivalent to being rationalizable by a continuous,
strictly increasing, sign-asymmetric numerical preference, and to being rationalizable
by a finite coherent coalitional multi-utility (CMU) function. Continuity of the
preference is joint, strict increase is in its first bundle argument, and every
component utility of the CMU witness is continuous, strictly increasing, and concave.

Import `MathEconLib.RevealedPreference.WGARP`. The declarations live in
`MathEconLib.RevealedPreference` and reuse its `Dataset`, affordability,
coordinatewise strict dominance, GARP, and finite Afriat theorem.

The proof first identifies WGARP with GARP on every two-observation restriction
(`wgarp_iff_pairwise_garp`). Finite Afriat supplies one continuous, concave,
strictly increasing utility for each ordered pair. Row-and-column coalitions
share members; their finite maximum of finite minimum utility differences gives
the coherent CMU rationalizer. Coherence guarantees that `r(x,y) ≥ 0` implies
`r(y,x) ≤ 0`, and that `r(x,y) > 0` implies `r(y,x) < 0`. These are the two
`SignAsymmetric` implications; they do not require numerical skew symmetry
`r(y,x) = -r(x,y)` or completeness of the nonnegative-score comparison.
Empty data use a single utility and a singleton coalition.

`finiteCMU_nonneg_iff` exposes the CMU comparison as existence of a coalition
whose every member weakly prefers the first bundle. `finiteCMU_const` recovers
`u x - u y` when all agents share utility `u`; diagonal scores simplify to zero.

`wgarp_iff_hasRegularPreferenceRationalization` exposes the preference
equivalence. `preferenceChoice` packages all available bundles whose numerical
comparison against every available alternative is nonnegative in the existing
`Choice.ChoiceFunction`. Here `0 ≤ r x y` means that `x` is at least as good as `y`;
the corresponding order orientation would be `R.le x y := 0 ≤ r y x`.
If that relation is a preorder, the selected bundles are greatest feasible
alternatives. Incomparability can leave the choice set empty. The theorem
`preferenceRationalizes_iff_mem_preferenceChoice` identifies rationalization with
observed membership on `budgetSet`; `wgarp_iff_exists_regular_preferenceChoice`
supplies that membership from WGARP. Choices retain ties. Rationalization
guarantees nonempty choice on observed budgets, without requiring transitivity
or imposing nonempty choice on every menu.

Ordinary utility is a specialization: `preferenceChoice_sub` identifies choice
from `u x - u y` with `utilityChoice u`, `preferenceRationalizes_sub_iff`
identifies its rationalization with `UtilityRationalizes`, and
`strictlyIncreasingFirst_sub_iff` identifies its strict increase with
`StrictlyIncreasing u`. These bridges require neither finite observations nor
regularity assumptions on the utility.

The numerical preferences and component utilities are defined on all of
`Bundle L`, while budgets contain only nonnegative bundles. The formalization
permits zero observed bundles and any nonnegative integer dimension `L : ℕ`,
including zero; commodity dimension is always finite. The representation
equivalences assume a finite observation type, including empty data. The
pairwise-GARP bridge and the necessity argument allow infinite observation types.
The generic CMU algebraic lemmas allow arbitrary alternative spaces; continuity
lemmas require a topology and monotonicity lemmas require a preorder, with the
stated regularity assumptions on participating agents.
Witness selection is noncomputable and supplies no numerical fitting algorithm.

The [checked examples](../MathEconLibExamples/RevealedPreference/WGARP.lean)
apply the characterization and choice bridge to the existing three-observation
cycle, which satisfies WGARP and violates GARP. Separate applications handle
expenditure ties and a prohibited binary reversal. The `disagreement` example
uses one coalition containing both utilities `u(x) = 2x₁ + x₂` and
`v(x) = x₁ + 2x₂`. The coalition is coherent and both components are continuous,
strictly increasing, and concave. Between `e₁ = (1,0)` and `e₂ = (0,1)`, both
directional CMU scores are `-1`. Thus neither weak comparison holds, numerical
skew symmetry fails, and `disagreement_preferenceChoice_empty` proves that the
actual `preferenceChoice` on `{e₁,e₂}` is empty. These are exact mathematical
examples; no empirical calibration or predictive claim is made.

## API migration

`WGARP` is now the direct binary-expenditure condition; we replace
`SatisfiesWGARP` with `WGARP`. The numerical sign predicate is named
`SignAsymmetric` instead of `Asymmetric`. Its contract still includes both
`0 ≤ r x y → r y x ≤ 0` and `0 < r x y → r y x < 0` for all bundles.
The characterization theorems retain their mathematical assumptions and
conclusions. The continuity and strict-increase aggregation lemmas now request
regularity only for agents belonging to the relevant coalitions. Callers with
global regularity can pass `fun _ i _ ↦ hu i` for the finite-CMU lemmas or
`fun i _ ↦ hu i` for the single-coalition lemmas. The supplied-witness and
existential rationalization predicates still require regularity of every
component utility.

## Sources and scope

Victor H. Aguiar, Per Hjertstrand, Roberto Serrano, and Özgür Evren (2026),
*[A Rationalization of the Weak Axiom of Revealed Preference](https://arxiv.org/abs/1906.00296v2)*,
arXiv:1906.00296v2, revised August 12, 2026, Theorem 1(i), (ii), and (iv),
is the mathematical source. This contribution uses
a finite coherent-CMU normal form for (ii). It adapts the Apache-2.0 Lean source
in [WGARP Lean](https://github.com/vaguiarl/wgarp-lean), including `TheoremOne`,
`Data`, `Necessity`, `FiniteCMU`, `FiniteConstruction`, and `ChoiceReviewBridge`.
The code attribution is Victor H. Aguiar; the mathematical attribution is to all
four paper authors. No manuscript text or other unlicensed project files are ported.

The paper assumes at least two goods and nonzero observed bundles; those
restrictions are unnecessary for these formal results. Its full six-way theorem,
the symmetric-matrix/simplex CMU representation and numerical skew symmetry,
and the pairwise Afriat/Varian certificate equivalences are outside this module's
scope. The reused Afriat theorem has its own bibliography in
[`Afriat.lean`](../MathEconLib/RevealedPreference/Afriat.lean).
