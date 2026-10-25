/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.IncompleteRankPreferencesDA
import MathEconLib.Matching.Classical.Marriage.RandomIncompletePreferences
import MathEconLib.ForMathlib.Uniform

/-!
# Incomplete acceptable lists can leave a balanced DA market unmatched

There is one proposer and one receiver. The proposer always accepts the receiver. In the
accepting profile the receiver reciprocates and DA matches the pair; in the rejecting profile
the receiver ranks `none` first and DA leaves both agents unmatched. Thus even the shorter
side need not be fully matched without the explicit acceptability hypotheses.

A fair coin selects these two profiles. The proposer's ordinal position is one when matched
and two when unmatched, giving expected average proposer rank `3/2`. The rejecting receiver's
outside rank is one, demonstrating that unmatched ranks depend on the agent's acceptable list.
All DA computations use the existing executable algorithm and kernel-checked finite evaluation.
-/

namespace MathEconLibExamples.Matching.IncompletePreferences

open MathEconLib.Matching.MarriageMarket
open MeasureTheory

/-- The sole potential partner is ranked above remaining unmatched. -/
def acceptingRanking : OptionalRanking 1 := OptionalRanking.ofComplete (Equiv.refl _)

/-- The outside option is first, so the only potential partner is unacceptable. -/
def rejectingRanking : OptionalRanking 1 :=
  acceptingRanking.trans (Equiv.swap 0 1)

/-- A one-by-one profile; `true` makes the receiver accept, `false` makes them reject. -/
def profile (accepts : Bool) : IncompleteRankProfile 1 1 :=
  ⟨fun _ ↦ acceptingRanking, fun _ ↦ if accepts then acceptingRanking else rejectingRanking⟩

/-- In the rejecting profile the proposer's interest is not reciprocated. -/
theorem receiver_rejects : ¬ (profile false).toMarriageMarket.AcceptableW 0 0 := by
  rw [IncompleteRankProfile.toMarriageMarket_acceptableW]
  decide +kernel

/-- In the accepting profile the pair is matched by the existing DA. -/
theorem da_accepting : (profile true).toMarriageMarket.galeShapleyComputable 0 = some 0 := by
  decide +kernel

/-- A balanced market with one unacceptable partner leaves the proposer unmatched. -/
theorem da_rejecting : (profile false).toMarriageMarket.galeShapleyComputable 0 = none := by
  decide +kernel

/-- The receiver is also unmatched when they reject the only possible partner. -/
theorem da_rejecting_symm :
    (profile false).toMarriageMarket.galeShapleyComputable.symm 0 = none := by
  decide +kernel

/-- The matched proposer receives ordinal rank one. -/
theorem totalRank_accepting :
    (profile true).totalProposerRank (profile true).toMarriageMarket.galeShapleyComputable = 1 := by
  decide +kernel

/-- The unmatched proposer receives their outside ordinal rank two. -/
theorem totalRank_rejecting :
    (profile false).totalProposerRank
      (profile false).toMarriageMarket.galeShapleyComputable = 2 := by
  decide +kernel

/-- The two equally likely profiles differ in the receiver's acceptable set. -/
noncomputable def law : PMF (IncompleteRankProfile 1 1) :=
  (PMF.uniformFintype Bool).map profile

/-- Equal probability of mutual acceptability and rejection gives expected ordinal rank `3/2`.
The statistic includes the unmatched proposer at their outside rank two. -/
theorem expectedAverageProposerRank_eq_three_halves :
    IncompleteRankProfile.expectedAverageProposerRank law
      (fun p ↦ p.toMarriageMarket.galeShapleyComputable) = (3 : ℝ) / 2 := by
  rw [IncompleteRankProfile.expectedAverageProposerRank, law,
    ← PMF.toMeasure_map _ _ Measurable.of_discrete]
  rw [integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable, PMF.integral_uniformOfFintype,
    Fintype.expect_eq_sum_div_card]
  simp only [IncompleteRankProfile.averageProposerRank_eq_total_div, Nat.cast_one, div_one,
    Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool]
  norm_num [totalRank_accepting, totalRank_rejecting]

end MathEconLibExamples.Matching.IncompletePreferences
