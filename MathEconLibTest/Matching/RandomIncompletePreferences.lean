/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLibExamples.Matching.IncompletePreferences
import MathEconLibExamples.Matching.RandomPreferences

/-! Public random-law applications and compatibility with the existing complete DA benchmark. -/

namespace MathEconLibTest.Matching.RandomIncompletePreferences

open MathEconLib.Matching.MarriageMarket

-- The new incomplete-list example actually runs DA and includes unmatched agents in expectation.
example : IncompleteRankProfile.expectedAverageProposerRank
    MathEconLibExamples.Matching.IncompletePreferences.law
      (fun p ↦ p.toMarriageMarket.galeShapleyComputable) = (3 : ℝ) / 2 :=
  MathEconLibExamples.Matching.IncompletePreferences.expectedAverageProposerRank_eq_three_halves

example :
    MathEconLibExamples.Matching.IncompletePreferences.rejectingRanking.rank none = 1 := by
  decide +kernel

example :
    MathEconLibExamples.Matching.IncompletePreferences.acceptingRanking.rank none = 2 := by
  decide +kernel

-- The complete two-by-two 5/4 example is unchanged under the incomplete-profile embedding.
example : IncompleteRankProfile.expectedAverageProposerRank
    (RankProfile.toIncompleteLaw (RankProfile.uniformProfile 2 2))
      (fun p ↦ p.toMarriageMarket.galeShapleyComputable) = (5 : ℝ) / 4 := by
  rw [RankProfile.expectedAverageProposerRank_toIncompleteLaw]
  simpa only [RankProfile.toIncomplete_toMarriageMarket] using
    MathEconLibExamples.Matching.RandomPreferences.expectedAverageProposerRank_two

-- Embedding arbitrary independent complete laws agrees with the new independent-law constructor.
example {m n : ℕ} (ν : ∀ a, PMF (RankProfile.Ranking m n a)) :
    RankProfile.toIncompleteLaw (RankProfile.independentProfile ν) =
      IncompleteRankProfile.independentProfile
        (fun a ↦ (ν a).map (RankProfile.rankingToIncomplete a)) :=
  RankProfile.toIncompleteLaw_independentProfile ν

example {m n : ℕ} (ν : ∀ a, PMF (IncompleteRankProfile.Ranking m n a)) :
    ProbabilityTheory.iIndepFun (fun a p ↦ IncompleteRankProfile.equivAgentRanks m n p a)
      (IncompleteRankProfile.independentProfile ν).toMeasure :=
  IncompleteRankProfile.iIndepFun_independentProfile ν

example {n : ℕ} (μ : PMF (IncompleteRankProfile 0 n))
    (outcome : IncompleteRankProfile 0 n → Fin 0 ≃. Fin n) :
    IncompleteRankProfile.expectedAverageProposerRank μ outcome = 0 := by
  simp

end MathEconLibTest.Matching.RandomIncompletePreferences
