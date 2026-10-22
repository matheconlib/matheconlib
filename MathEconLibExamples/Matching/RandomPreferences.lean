/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.RandomPreferencesUniform
import MathEconLib.Matching.Classical.Marriage.RankPreferencesDA

/-!
# The two-by-two proposer DA benchmark

Under independent uniform rankings, the two proposers have different first choices with
probability `1/2`, giving average proposer rank `1`. Otherwise they share a first choice: one
gets that partner and the other gets their second choice, giving average rank `3/2`.
Thus the expectation is `(1/2) * 1 + (1/2) * (3/2) = 5/4`.

The kernel checks all sixteen profiles using the existing executable proposer DA. This samples
preference profiles and then runs DA; it does not select uniformly among stable matchings. The
benchmark concerns ordinal rank, with rank one best, rather than cardinal welfare.

The independent uniform model is classical; see Boris Pittel (1989), *The Average Number of
Stable Matchings*, https://doi.org/10.1137/0402048. That reference studies stable-matching counts
and asymptotic ranks; the elementary `5/4` calculation here is proved directly, without claiming
that the paper states this exact finite value. Profile-code provenance is in `RankPreferences`.
-/

namespace MathEconLibExamples.Matching.RandomPreferences

open MathEconLib.Matching.MarriageMarket
open RankProfile
open scoped BigOperators

set_option maxRecDepth 4096 in
/-- Exact finite evaluation of the existing executable DA on all sixteen two-by-two profiles.
With different proposer first choices, DA gives each their first choice (eight profiles).
With a shared first choice, one proposer receives rank one and the other rank two (eight profiles).
The kernel checks this finite calculation; no external computation supplies the proof. -/
theorem sum_totalProposerRank_two :
    (∑ p : RankProfile 2 2,
      p.totalProposerRank p.toMarriageMarket.galeShapleyComputable) = 40 := by
  decide +kernel

/-- Under independent uniform complete strict rankings in the two-by-two marriage market,
the existing executable proposer DA has expected average one-based proposer rank `5/4`.
This is a finite ordinal-rank benchmark, not a cardinal welfare or asymptotic claim. -/
theorem expectedAverageProposerRank_two :
    expectedAverageProposerRank (uniformProfile 2 2)
      (fun p ↦ p.toMarriageMarket.galeShapleyComputable) = 5 / 4 := by
  rw [expectedAverageProposerRank_uniform_eq_sum, ← Nat.cast_sum, sum_totalProposerRank_two, card]
  norm_num

end MathEconLibExamples.Matching.RandomPreferences
