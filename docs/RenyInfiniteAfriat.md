# Infinite Afriat and compactness

Import `MathEconLib.RevealedPreference` and open
`MathEconLib.RevealedPreference`.

`infinite_reny_characterization` proves all three clauses of Reny's
characterization. For any positive finite commodity dimension `L`, arbitrary
observation type `T`, nonnegative nonzero prices `p : T → Bundle L`, and
nonnegative choices `q : T → Bundle L`, it proves

```lean
((∃ u : Utility L, rawRenyRationalizes p q u) ↔ GraphGARP p q) ∧
  (GraphGARP p q ↔ HasRegularRenyRationalization p q)
```

`rawRenyRationalizes` requires weak utility comparisons for affordable bundles
and strict comparisons for strictly cheaper bundles. The regularity package
adds monotonicity, quasiconcavity, and strict increase when **every** coordinate
increases. No finiteness or countability assumption is imposed on `T`.
Utilities are represented on all real bundles; economic requirements apply to
the nonnegative orthant. Empty data, zero choices, zero income, and free goods
are permitted. Continuity, concavity, and unique demand are not conclusions.

## Proof dependencies

1. The merged finite GARP certificate and Afriat envelope API gives a finite
   continuous concave rationalization. `RenyFinite` supplies the additional
   nonnegative-price monotonicity and semistrictness lemmas and handles empty data.
2. Countability of rational strong pairs gives one positive dyadic margin
   schedule whose mass over every finite set is at most one half.
3. A bounded scalar baseline and finitely many utility-threshold jumps normalize
   each finite witness. The transformation preserves utility comparisons and
   quasiconcavity while imposing the prescribed margins.
4. Closed constraints have a simultaneous solution in the compact product of
   ordinary real intervals `[0,1]`. Rational density and monotonicity recover
   semistrict increase; a budget-slack argument recovers strict affordability.

The public invariant
`InfiniteAfriat.exists_uniform_margins_and_finite_witnesses` has quantifier order
`∃ w, (∀ r, 0 < w r) ∧ … ∧ ∀ finite s, ∃ v, …`.
The same schedule is used by every finite witness. Margins can vary across pairs;
they are not a single positive scalar lower bound.

A direct infinite envelope of affine supports would require additional
boundedness control and would not supply this characterization. A first-order
syntax/model route introduces a real-valued representation problem. The chosen
standard-real cube route uses the smaller dependency chain above and reuses
Mathlib compactness directly.

`MathEconLib.ForMathlib.LogicalCompactness` also provides finite-valued
finite-local compactness, its Boolean specialization, and a faithful-description
scaling implication. The closed-constraint helper is a thin convenience wrapper
around Mathlib's compact finite-intersection theorem, not new mathematics or a
claim that every finite economic theorem scales.

## Checked consumers

[The infinite example](../MathEconLibExamples/RevealedPreference/RenyInfinite.lean)
constructs infinitely many distinct observations with a free good and zero
income, proves admissibility and GARP, and applies the named infinite theorem.
[API and regression tests](../MathEconLibTest/RevealedPreference/InfiniteAfriat.lean)
include an empty dataset, three-valued infinite constraints, the fixed-margin
invariant, and the boundary example `0 < x ≤ 1/(n+1)`: every finite subfamily
is feasible, but the whole family has no positive feasible point.
These are exact mathematical instances, not empirical calibration or prediction
claims. Run the repository's import checks, `lake build`, and
`python3 scripts/check-proof-integrity.py` for acceptance.

## Sources and scope

Philip J. Reny (2015), *A Characterization of Rationalizable Consumer Behavior*,
Econometrica **83**(1), 175–192, Theorem 1,
[doi:10.3982/ECTA12345](https://doi.org/10.3982/ECTA12345).

Yannai A. Gonczarowski, Scott Duke Kominers, and Ran I. Shorrer (2025),
*To infinity and beyond: A general framework for scaling economic theories*,
Theoretical Economics **20**(2), 511–542, Lemma 1 and Theorem 8,
[doi:10.3982/TE5878](https://doi.org/10.3982/TE5878).
The formalization adapts their prescribed-gap architecture through finite scalar
normalization and a real cube; it does not reproduce their propositional utility
syntax or formalize all applications in that paper.

Lean implementation ported from Victor H. Aguiar's Apache-2.0
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean) development. The economic
results and compactness architecture are credited to the sources above.
