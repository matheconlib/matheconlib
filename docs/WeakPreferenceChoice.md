# Finite choice with ties

This is the first implementation milestone of [#200](https://github.com/matheconlib/matheconlib/issues/200).
The public entry point is `MathEconLib.Choice`.

Preferences use an explicit Mathlib `Preorder`, with larger alternatives weakly preferred.
`pref.lt` expresses strict preference and `AntisymmRel pref.le` expresses indifference.
Completeness is a separate `Std.Total pref.le` proof, supplied to finite-existence and
refinement results. No preference carrier or behavioral typeclass is introduced.

`maximizers` is the set of Mathlib `IsGreatest` witnesses. For a represented bundle family,
`optimalBundles` maps those witnesses to a family of sets. Distinct tied bundles stay separate.
`mem_optimalBundles_iff` exposes representation, feasibility and weak optimality without
requiring clients to unpack the image construction.
The representation embedding ensures that a finite menu has only finitely many feasible
represented bundles, even when the bundle-index type is infinite.

`Order.tieBreakOrder` composes Mathlib's antisymmetrization, lexicographic product and injective
order lift. A fixed priority resolves indifference while preserving strict preferences.
`ChoiceFunction.ofWeakBundleOrder` then reuses `ofBundleOrder`. Its finite optimality theorem
requires a feasible represented bundle; strict preferences recover the original constructor.
The general theorem `ofBundleOrder_mem_optimalBundles_of_finite_feasible` accepts any linear
refinement preserving weak comparisons and a finite nonempty family of feasible indices.
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

For a value function into any preordered type, `mem_maximizers_lift` proves
`a ∈ maximizers (Preorder.lift value) S ↔ a ∈ S ∧ IsMaxOn value S a`.
Mathlib's `IsMaxOn` alone does not require `a ∈ S`; the feasibility conjunct is essential.
This bridge connects ordinal preferences to value-based optimization without assuming every
preference admits a cardinal representation.

[#177](https://github.com/matheconlib/matheconlib/issues/177) proposes a shared value-induced
choice and game-theory best-response API using `IsMaxOn`. The checked client
`MathEconLibTest/Choice/WeakPreferencesGame.lean` expresses the existing strategic-game Nash
condition as each incumbent action belonging to its unilateral-payoff maximizer set.
This establishes the connection without introducing another best-response definition or
implementing the rest of #177. Shared naming and placement remain for maintainer review.

[#161](https://github.com/matheconlib/matheconlib/issues/161) is assigned to Daniel to select
source material and a first application. At the 22 October 2026 audit it specifies neither a
source revision nor a proposed interface, and has no discussion comments. This PR imports no
external preference implementation and leaves the existing strict choice, feasible-bundle,
and marriage preference APIs unchanged. The shared representation and public names should be
reviewed with that port before this draft is made ready.

The worked examples cover utility net of transfers, incompatible tied singleton bundles,
and alternative participation conventions at an outside-option tie. Correspondence versions
of substitutability/IRC and matching stability remain later milestones of #200. The small
process-level refinement interface in #139 does not depend on completing those milestones.
