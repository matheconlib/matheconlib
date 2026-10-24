/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching
import MathEconLib.Probability.FinDist.Measure
import MathEconLibExamples.Matching.RandomPreferences

/-!
Joint-law clients import the independent and correlated worked examples without duplicating them.
-/

namespace MathEconLibTest.Matching.RandomPreferencesUniform

open MathEconLib.Matching.MarriageMarket
open RankProfile
open MathEconLibExamples.Matching.RandomPreferences
open scoped BigOperators

example : expectedAverageProposerRank (uniformProfile 2 2)
    (fun p ↦ p.toMarriageMarket.galeShapleyComputable) = (5 : ℝ) / 4 :=
  MathEconLibExamples.Matching.RandomPreferences.expectedAverageProposerRank_two

-- The same individual uniform marginals can yield dependent rankings and a different expectation.
example (a : Fin 2 ⊕ Fin 2) :
    Correlated.law.map (fun p ↦ equivAgentRanks 2 2 p a) =
      PMF.uniformFintype (Ranking 2 2 a) := Correlated.law_map_ranking a

example : ¬ ProbabilityTheory.IndepFun (fun p : RankProfile 2 2 ↦ p.manRank 0)
    (fun p ↦ p.manRank 1) Correlated.law.toMeasure := Correlated.not_indepFun

example : expectedAverageProposerRank Correlated.law
    (fun p ↦ p.toMarriageMarket.galeShapleyComputable) = (3 : ℝ) / 2 :=
  Correlated.expectedAverageProposerRank_eq_three_halves

example : expectedAverageProposerRank (uniformProfile 0 0)
    (fun p ↦ p.toMarriageMarket.galeShapleyComputable) = 0 := by simp

-- Empty populations still have one full profile and a normalized law.
example : Fintype.card (RankProfile 0 0) = 1 := by rw [card]; norm_num

example (p : RankProfile 0 0) : uniformProfile 0 0 p = 1 := by
  simp [uniformProfile_apply]

-- The standard probability API applies to the whole family, including the empty product.
example {m n : ℕ} :
    (uniformProfile m n).toMeasure.map (equivAgentRanks m n) =
      MeasureTheory.Measure.pi
        (fun a ↦ (PMF.uniformFintype (Ranking m n a)).toMeasure) :=
  uniformProfile_map_agentRanks m n

example : ProbabilityTheory.iIndepFun (fun a p ↦ equivAgentRanks 0 0 p a)
    (uniformProfile 0 0).toMeasure := iIndepFun_uniformProfile 0 0

-- This is cross-side independence, not merely independence within each population.
example {m n : ℕ} (i : Fin m) (j : Fin n) :
    ProbabilityTheory.IndepFun (fun p : RankProfile m n ↦ p.manRank i)
      (fun p ↦ p.womanRank j) (uniformProfile m n).toMeasure :=
  (iIndepFun_uniformProfile m n).indepFun (i := Sum.inl i) (j := Sum.inr j) (by simp)

-- Agents on a nonempty side facing no partners have the unique permutation of `Fin 0`.
example : (uniformProfile 0 2).toMeasure.map (fun p ↦ p.womanRank 0) =
    (PMF.uniformFintype (Equiv.Perm (Fin 0))).toMeasure :=
  uniformProfile_map_womanRank 0

example : (uniformProfile 2 0).toMeasure.map (fun p ↦ p.manRank 0) =
    (PMF.uniformFintype (Equiv.Perm (Fin 0))).toMeasure :=
  uniformProfile_map_manRank 0

-- In an unequal market the ranking law still uses the opposite population's size.
example : (uniformProfile 1 2).toMeasure.map (fun p ↦ p.manRank 0) =
    (PMF.uniformFintype (Equiv.Perm (Fin 2))).toMeasure :=
  uniformProfile_map_manRank 0

-- The one-agent market returns its only partner, with rank one.
example : expectedAverageProposerRank (uniformProfile 1 1)
    (fun p ↦ p.toMarriageMarket.galeShapleyComputable) = 1 := by
  have h : (∑ p : RankProfile 1 1,
      p.totalProposerRank p.toMarriageMarket.galeShapleyComputable) = 1 := by decide +kernel
  rw [expectedAverageProposerRank_uniform_eq_sum, ← Nat.cast_sum, h, card]
  norm_num

example (p : RankProfile 1 2) : uniformProfile 1 2 p = (2 : ENNReal)⁻¹ := by
  simp [uniformProfile_apply]

-- The benchmark law also uses the library's finite-distribution representation directly.
example (n : ℕ) : expectedAverageProposerRank (uniformProfile n n)
    (fun p ↦ p.toMarriageMarket.galeShapleyComputable) =
    (MathEconLib.Probability.FinDist.uniform (α := RankProfile n n)).expect
      (fun p ↦ p.averageProposerRank p.toMarriageMarket.galeShapleyComputable) := by
  rw [expectedAverageProposerRank, uniformProfile, PMF.integral_uniformOfFintype,
    MathEconLib.Probability.FinDist.expect_uniform]

example (m n : ℕ) :
    independentProfile (fun a ↦ PMF.uniformFintype (Ranking m n a)) = uniformProfile m n :=
  independentProfile_uniform m n

#print axioms MathEconLibExamples.Matching.RandomPreferences.expectedAverageProposerRank_two
#print axioms RankProfile.uniformProfile_apply_eq_prod
#print axioms RankProfile.uniformProfile_map_agentRanks
#print axioms RankProfile.uniformProfile_map_ranking
#print axioms RankProfile.iIndepFun_uniformProfile
#print axioms RankProfile.independentProfile_uniform
#print axioms Correlated.law_map_ranking
#print axioms Correlated.not_indepFun
#print axioms Correlated.expectedAverageProposerRank_eq_three_halves

end MathEconLibTest.Matching.RandomPreferencesUniform
