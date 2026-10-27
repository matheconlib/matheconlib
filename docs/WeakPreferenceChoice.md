# Finite choice with ties

This is the first implementation milestone of [#200](https://github.com/matheconlib/matheconlib/issues/200).
The public entry point is `MathEconLib.Choice`.

Preferences use the explicit `Preference` interface from `MathEconLib.Preferences`, with larger
alternatives weakly preferred. `pref.lt` expresses strict preference and `AntisymmRel pref.le`
expresses indifference. `CompletePreference` extends this interface with totality; it is used
by finite-existence results and fixed tie-breaking. Base correspondences allow incomparability.

`maximizers` is the set of Mathlib `IsGreatest` witnesses. For a represented bundle family,
`optimalBundles` maps those witnesses to a family of sets. Distinct tied bundles stay separate.
`mem_optimalBundles_iff` exposes representation, feasibility and weak optimality without
requiring clients to unpack the image construction.
The representation embedding ensures that a finite menu has only finitely many feasible
represented bundles, even when the bundle-index type is infinite.

`CompletePreference.tieBreak` reuses `Order.tieBreakOrder`, which composes Mathlib's
antisymmetrization, lexicographic product and injective order lift. A fixed priority resolves
indifference while preserving strict preferences.
`ChoiceFunction.ofWeakBundleOrder` then reuses `ofBundleOrder`. Its finite optimality theorem
requires a feasible represented bundle; strict preferences recover the original constructor.
The general theorem `ofBundleOrder_mem_optimalBundles_of_finite_feasible` accepts any linear
refinement preserving weak comparisons and a finite nonempty family of feasible indices.
Such a comparison-preserving linear refinement already implies completeness of the original
preference. This theorem does not complete missing comparisons in an incomplete preference.
The menu may be infinite; the finite-menu result is a corollary. An example represents just
two singleton bundles on the menu of all natural numbers. Optional-partner selection inherits
unit demand directly from the existing `unitDemand_ofOptionLinearOrder` theorem.
The existing `bestOption` selector also returns a weak maximizer under the refinement.
The new refinement uses classical reasoning and is noncomputable; this is a semantic selection
API, not a new executable enumeration algorithm.

An empty maximizer family reports no greatest feasible witness. It is different from a family
containing the empty bundle. Infinite menus can fail to attain a greatest element, and finite
incomplete preferences can lack one. The selected `ChoiceFunction` retains the existing
constructor's empty-set totalization; its optimality conclusion has explicit attainment
hypotheses. Weak attainment alone is insufficient: an infinite all-tied regression has every
singleton weakly optimal, but increasing natural-number priorities have no maximum. The
selector then returns the empty set, which is not represented and is not weakly optimal.

## Shared optimization and the preference port

For a value function into any preordered type, `mem_maximizers_ofUtility` proves
`a ∈ maximizers (Preference.ofUtility value) S ↔ a ∈ S ∧ IsMaxOn value S a`.
Mathlib's `IsMaxOn` alone does not require `a ∈ S`; the feasibility conjunct is essential.
This bridge connects ordinal preferences to value-based optimization without assuming every
preference admits a cardinal representation.

`Preference.IsRepresentedBy.mem_maximizers_iff` derives the same characterization from a supplied
ordinal representation. `CompletePreference.exists_nat_utility_maximizers` applies the finite
representation theorem from the preference layer: one natural-number utility describes the
greatest alternatives on every menu. Neither result identifies expected-utility or utilitarian
welfare comparisons under arbitrary changes of representing utility.

[#177](https://github.com/matheconlib/matheconlib/issues/177) proposes a shared value-induced
choice and game-theory best-response API using `IsMaxOn`. The checked client
`MathEconLibTest/Choice/WeakPreferencesGame.lean` expresses the existing strategic-game Nash
condition as each incumbent action belonging to its unilateral-payoff maximizer set.
This establishes the connection without introducing another best-response definition or
implementing the rest of #177. Shared naming and placement remain for maintainer review.

The preference dependency is [#253](https://github.com/matheconlib/matheconlib/pull/253) at
[`76c5148`](https://github.com/matheconlib/matheconlib/commit/76c514848d5401b2586b0f88f1c19c46ee3c88c7),
proposed under [#161](https://github.com/matheconlib/matheconlib/issues/161). This local stack uses
that proposed interface; it does not record approval or merging of #253. Existing strict choice
constructors, `Order.tieBreakOrder`, and marriage preference APIs keep their signatures.

## API migration to the preference layer

The signature changes below replace independently supplied order laws with the agreed named
preference objects. Weak comparisons, feasible sets, priorities, and economic conclusions are
preserved. No implicit conversion from arbitrary Mathlib preorders to preferences is installed.

| API | Before | After |
| --- | --- | --- |
| `maximizers`, `mem_maximizers`, `maximizers_subset`, `maximizers_empty`, `indifferent_of_mem_maximizers` | Explicit `Preorder` | Explicit `Preference`; use `Preference.ofPreorder p` for an existing order. |
| `optimalBundles`, `mem_optimalBundles_iff`, `subset_of_mem_optimalBundles` | Explicit `Preorder` | Explicit `Preference`, including incomplete preferences. |
| `maximizers_nonempty_of_finite`, `optimalBundles_nonempty_of_finite`, `optimalBundles_nonempty_of_finite_feasible` | `Preorder` and a separate `Std.Total` proof | One `CompletePreference`; remaining feasibility and finiteness hypotheses are unchanged. |
| `ofBundleOrder_mem_optimalBundles_of_finite_feasible` | A `Preorder` and a comparison-preserving linear refinement | A `Preference` with the same refinement, comparison, feasibility, and finiteness hypotheses. |
| `ofWeakBundleOrder`, `ofWeakBundleOrder_eq_of_max`, `ofWeakBundleOrder_mem_optimalBundles_of_finite`, `bestOption_mem_maximizers` | `Preorder` and a separate completeness argument | One `CompletePreference`; the separate completeness argument is removed. |
| `ofWeakBundleOrder_linearOrder` | The selector is applied to `L.toPreorder` and a totality proof | The selector is applied to `CompletePreference.ofLinearOrder L`; the supplied linear order and priority are unchanged. |
| Value-induced maximizers | `maximizers (Preorder.lift value)` | `maximizers (Preference.ofUtility value)`, characterized by `mem_maximizers_ofUtility`. |
| `mem_maximizers_lift` | A lifted preorder is passed directly | The name is retained for the explicit `Preference.ofPreorder (Preorder.lift value)` form, proved by the canonical utility lemma. |

Use `CompletePreference.ofPreorder p h` to package an existing complete preorder, or
`CompletePreference.ofUtility value` for a utility valued in a total preorder. A complete
preference coerces to its underlying `Preference`; `.toPreference` is also available when the
bundle-index type needs to be made explicit during elaboration.

The worked examples' `pref` definitions now return `CompletePreference`; their named `complete`
proofs remain available. The incomplete two-alternative regression uses `Preference` and still
has two maximal alternatives and no greatest alternative. The game client retains an arbitrary
preordered payoff codomain, so the utility bridge does not assume completeness or antisymmetry.

The worked examples cover utility net of transfers, incompatible tied singleton bundles,
and alternative participation conventions at an outside-option tie. Correspondence versions
of substitutability/IRC and matching stability remain later milestones of #200. The small
process-level refinement interface in #139 does not depend on completing those milestones.
