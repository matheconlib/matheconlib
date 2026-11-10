# Finite WGARP rationalization

For a finite dataset with strictly positive prices and nonnegative
observed bundles, WGARP is equivalent to rationalization by a continuous,
strictly increasing, sign-asymmetric numerical preference, and to rationalization
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
the coherent CMU rationalizer. Coherence supplies both weak and strict sign
asymmetry implications. Empty data use a single utility and a singleton coalition.
Coherence does not assert numerical skew symmetry.

`wgarp_iff_hasRegularPreferenceRationalization` exposes the preference
equivalence. `preferenceChoice` packages all available bundles whose numerical
comparison against every available alternative is nonnegative in the existing
`Choice.ChoiceFunction`. The theorem
`preferenceRationalizes_iff_mem_preferenceChoice` identifies rationalization with
observed membership on `budgetSet`; `wgarp_iff_exists_regular_preferenceChoice`
supplies that membership from WGARP. Choices retain ties. Rationalization
guarantees nonempty choice on observed budgets, without requiring transitivity
or imposing nonempty choice on every menu.

The numerical preferences and component utilities are defined on all of
`Bundle L`, while budgets contain only nonnegative bundles. The formalization
permits zero observed bundles and any natural-number dimension, including zero.
The representation equivalences assume a finite observation type, including empty data;
the pairwise-GARP bridge and the necessity argument need no finiteness assumption.
Witness selection is noncomputable and supplies no numerical fitting algorithm.

The [checked examples](../MathEconLibExamples/RevealedPreference/WGARP.lean)
apply the characterization and choice bridge to the existing three-observation
cycle, which satisfies WGARP and violates GARP. Separate applications handle
expenditure ties and a prohibited binary reversal. These are exact illustrative
datasets; no empirical calibration or predictive claim is made.

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
