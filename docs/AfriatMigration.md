# Afriat order aliases

The revealed-preference API now defines `Nonnegative x` as `0 ≤ x`,
`StrictDominates x z` as `z < x`, and `StrictlyIncreasing u` as `StrictMono u`.
These are thin aliases for the existing product order on bundles. Strict
dominance still means weak improvement in every coordinate and inequality of
the bundles; it does not require strict improvement in every coordinate.
The theorem statements and economic assumptions are unchanged.

Strict increase is global on `Bundle L`; affordability still restricts candidate
bundles to the nonnegative orthant. Reny's `SemiStrictlyIncreasingOnNonnegative`
in [#302](https://github.com/matheconlib/matheconlib/pull/302) is a separate condition:
it compares nonnegative bundles whose every coordinate increases strictly. In
positive dimension it is weaker than `StrictlyIncreasing`. With zero commodities,
`StrictlyIncreasing` is vacuous, while the all-coordinate semistrict condition
would require a strict utility increase from the unique bundle to itself and is
therefore impossible.

The bridge names `strictDominates_iff_lt` and
`strictlyIncreasing_iff_strictMono` remain available. Downstream proofs that
unfold the old definitions should use these bridges and Mathlib's order API.
To recover the old dominance conjunction, use `lt_iff_le_and_ne` and reverse
the inequality-of-bundles condition with `Ne.symm`. Proofs that explicitly
introduce the two bundle arguments of `StrictlyIncreasing` should use
`StrictMono`'s order: the smaller bundle first, then the larger bundle.
When casting a coordinate inequality from `Nonnegative`, give the scalar
inequality an explicit type before `exact_mod_cast`; this reduces the
function zero to the scalar zero.

`GARP D` now directly abbreviates `GraphGARP D.price D.choice`. The redundant
public name `SatisfiesGARP` is removed; replace references with `GARP` and
remove it from unfolding lists. Dataset restrictions, graph reachability,
Afriat certificates, and rationalization conclusions retain their existing
meaning.

The public-import checks in
[`Compatibility.lean`](../MathEconLibTest/RevealedPreference/Compatibility.lean)
pin both the definitional aliases and their coordinatewise economic contracts,
including vacuous strict increase with zero commodities. The existing concrete
Afriat applications and theorem signatures remain checked clients.
