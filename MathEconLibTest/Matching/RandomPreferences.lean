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

#print axioms RankProfile.expectedAverageProposerRank_two
#print axioms RankProfile.uniformProfile_apply_eq_prod
#print axioms MathEconLib.Matching.MarriageMarket.IsStableMatching.isSome_of_card_eq

end MathEconLibTest.Matching.RandomPreferences
