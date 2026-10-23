# Finite choice with ties

This is the first implementation milestone of [#200](https://github.com/matheconlib/matheconlib/issues/200).
The public entry point is `MathEconLib.Choice`.

Preferences use an explicit Mathlib `Preorder`, with larger alternatives weakly preferred.
`pref.lt` expresses strict preference and `AntisymmRel pref.le` expresses indifference.
Completeness is a separate `Std.Total pref.le` proof, supplied to finite-existence and
refinement results. No preference carrier or behavioral typeclass is introduced.

`maximizers` is the set of Mathlib `IsGreatest` witnesses. For a represented bundle family,
`optimalBundles` maps those witnesses to a family of sets. Distinct tied bundles stay separate.
The representation embedding ensures that a finite menu has only finitely many feasible
represented bundles, even when the bundle-index type is infinite.

`Order.tieBreakOrder` composes Mathlib's antisymmetrization, lexicographic product and injective
order lift. A fixed priority resolves indifference while preserving strict preferences.
`ChoiceFunction.ofWeakBundleOrder` then reuses `ofBundleOrder`. Its finite optimality theorem
requires a feasible represented bundle; strict preferences recover the original constructor.
The existing `bestOption` selector also returns a weak maximizer under the refinement.
The new refinement uses classical reasoning and is noncomputable; this is a semantic selection
API, not a new executable enumeration algorithm.

An empty maximizer family reports no greatest feasible witness. It is different from a family
containing the empty bundle. Infinite menus can fail to attain a greatest element, and finite
incomplete preferences can lack one. The selected `ChoiceFunction` retains the existing
constructor's empty-set totalization; its optimality conclusion has explicit attainment
hypotheses.

## Overlap with the preference port in #161

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
