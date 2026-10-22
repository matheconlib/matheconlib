/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib

/-!
Public-import checks for random-preference marriage markets. These exercise the actual DA,
empty and one-agent boundaries, and the direction and population size of ordinal ranks.
-/

namespace MathEconLibTest.Matching.RandomPreferences

open MathEconLib.Matching.MarriageMarket
open RankProfile
open scoped BigOperators

example : expectedAverageProposerRank 2 = (5 : ℝ) / 4 :=
  expectedAverageProposerRank_two

example : expectedAverageProposerRank 0 = 0 := expectedAverageProposerRank_zero

-- Empty populations still have one full profile and a normalized law.
example : Fintype.card (RankProfile 0 0) = 1 := by rw [card]; norm_num

example (p : RankProfile 0 0) : uniformProfile 0 0 p = 1 := by
  simp [uniformProfile_apply]

-- The one-agent market returns its only partner, with rank one.
example : expectedAverageProposerRank 1 = 1 := by
  have h : (∑ p : RankProfile 1 1,
      p.totalProposerRank p.toMarriageMarket.galeShapleyComputable) = 1 := by decide +kernel
  rw [expectedAverageProposerRank_eq_sum, ← Nat.cast_sum, h, card]
  norm_num

-- Smaller positions are better, and the adapter supplies that order to the existing API.
example (p : RankProfile 2 2) (i : Fin 2) :
    p.toMarriageMarket.ltM i (some ((p.manRank i).symm 1))
      (some ((p.manRank i).symm 0)) := by simp [rank]

example (p : RankProfile 2 2) (i : Fin 2) :
    (p.toMarriageMarket.galeShapleyComputable i).isSome := isSome_galeShapleyComputable p i

example (p : RankProfile 2 2) (j : Fin 2) :
    (p.toMarriageMarket.galeShapleyComputable.symm j).isSome :=
  isSome_symm_galeShapleyComputable p j

-- Unequal-size adapters use the opposite population's size for the outside option.
example (p : RankProfile 1 2) : rank (p.manRank 0) none = 3 := rfl

example (p : RankProfile 1 2) (j : Fin 2) : rank (p.womanRank j) none = 2 := rfl

example (p : RankProfile 1 2) : uniformProfile 1 2 p = (2 : ENNReal)⁻¹ := by
  simp [uniformProfile_apply]

example (p : RankProfile 1 2) :
    p.toMarriageMarket.IsStableMatching p.toMarriageMarket.galeShapleyComputable :=
  p.toMarriageMarket.stable_galeShapleyComputable

-- Balance is unnecessary for the average, or for completeness of the short side.
example (p : RankProfile 1 2) (μ : Fin 1 ≃. Fin 2) :
    p.averageProposerRank μ = (p.totalProposerRank μ : ℝ) := by
  simp [averageProposerRank_eq_total_div]

example (p : RankProfile 1 2) (i : Fin 1) :
    (p.toMarriageMarket.galeShapleyComputable i).isSome :=
  isSome_galeShapleyComputable_of_le p (by decide) i

example (p : RankProfile 2 1) (j : Fin 1) :
    (p.toMarriageMarket.galeShapleyComputable.symm j).isSome :=
  isSome_symm_galeShapleyComputable_of_le p (by decide) j

-- On the long side completeness fails: this DA leaves the second proposer unmatched.
example : ((default : RankProfile 2 1).toMarriageMarket.galeShapleyComputable 1) = none := by
  decide +kernel

-- The stronger general theorem needs no individual-rationality hypothesis.
example {M W : Type*} [Fintype M] [Fintype W]
    (mkt : MathEconLib.Matching.MarriageMarket M W) {μ : M ≃. W}
    (hμ : mkt.Unblocked μ) (hcard : Fintype.card M ≤ Fintype.card W)
    (hM : ∀ m w, mkt.AcceptableM m w) (hW : ∀ w m, mkt.AcceptableW w m) (m : M) :
    (μ m).isSome := Unblocked.isSome_of_card_le mkt hμ hcard hM hW m

-- Rank comparisons use the existing economic preference and DA optimality interfaces.
example {m n : ℕ} (p : RankProfile m n) {ν : Fin m ≃. Fin n}
    (hν : p.toMarriageMarket.IsStableMatching ν) :
    p.averageProposerRank p.toMarriageMarket.galeShapleyComputable ≤ p.averageProposerRank ν :=
  averageProposerRank_galeShapleyComputable_le p hν

-- Side exchange also turns existing receiver pessimality into a rank-statistic comparison.
example {m n : ℕ} (p : RankProfile m n) {ν : Fin m ≃. Fin n}
    (hν : p.toMarriageMarket.IsStableMatching ν) :
    p.symm.averageProposerRank ν.symm ≤
      p.symm.averageProposerRank p.toMarriageMarket.galeShapleyComputable.symm := by
  apply p.symm.averageProposerRank_le
  exact p.toMarriageMarket.galeShapleyComputable_womanPessimal hν

example {m n : ℕ} (p : RankProfile m n) {μ ν : Fin m ≃. Fin n}
    (h : p.toMarriageMarket.MenWeaklyPrefer μ ν) :
    p.totalProposerRank μ ≤ p.totalProposerRank ν := p.totalProposerRank_le h

example {m n : ℕ} (p : RankProfile m n) (μ : Fin m ≃. Fin n) :
    p.symm.symm.averageProposerRank μ = p.averageProposerRank μ := by simp

-- The benchmark law also uses the library's finite-distribution representation directly.
example (n : ℕ) : expectedAverageProposerRank n =
    (MathEconLib.Probability.FinDist.uniform (α := RankProfile n n)).expect
      (fun p ↦ p.averageProposerRank p.toMarriageMarket.galeShapleyComputable) := by
  rw [expectedAverageProposerRank, uniformProfile, PMF.integral_uniformOfFintype,
    MathEconLib.Probability.FinDist.expect_uniform]

#print axioms RankProfile.expectedAverageProposerRank_two
#print axioms RankProfile.uniformProfile_apply_eq_prod
#print axioms MathEconLib.Matching.MarriageMarket.IsStableMatching.isSome_of_card_eq
#print axioms MathEconLib.Matching.MarriageMarket.Unblocked.isSome_of_card_le
#print axioms PEquiv.isSome_of_forall_symm_isSome_of_card_le
#print axioms RankProfile.averageProposerRank_galeShapleyComputable_le

end MathEconLibTest.Matching.RandomPreferences
