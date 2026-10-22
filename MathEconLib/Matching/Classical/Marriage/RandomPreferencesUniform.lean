/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.RandomPreferences
import MathEconLib.ForMathlib.Uniform

/-!
# Independent uniform preference rankings

This specialization of `RandomPreferences` gives every agent an independent uniform strict
ranking of the opposite population. The full profile law, its product-law description, all
marginals, and joint independence agree, including empty and unequal populations. The shared
finite-uniform identities live in `ForMathlib.Uniform`. The worked two-by-two DA benchmark is in
`MathEconLibExamples.Matching.RandomPreferences`.

The profile representation and uniform law adapt the Formal Conjectures source recorded in
`RankPreferences`. The independent uniform model is also used in Ashlagi, Kanoria and Leshno
(2017), Section II.A, https://doi.org/10.1086/689869. Asymptotic results are outside this module.
-/

namespace MathEconLib.Matching.MarriageMarket

namespace RankProfile

variable {m n : ℕ}

open MeasureTheory
open scoped BigOperators

/-- Independent uniform rankings for both populations, as the uniform law on all rank profiles.
This adapts `StableMarriage.uniformProfile` from the source cited in `RankPreferences`. -/
noncomputable def uniformProfile (m n : ℕ) : PMF (RankProfile m n) :=
  PMF.uniformOfFintype (RankProfile m n)

/-- Every full profile has equal mass. -/
theorem uniformProfile_apply (p : RankProfile m n) :
    uniformProfile m n p =
      (((Nat.factorial n) ^ m * (Nat.factorial m) ^ n : ℕ) : ENNReal)⁻¹ := by
  simp [uniformProfile, PMF.uniformOfFintype_apply, card]

/-- The full joint mass factors into the uniform masses of all individual rankings.
Because `equivRanks` is a bijection onto unrestricted ranking families, this characterizes
independent uniform preference lists, rather than only normalization of the joint law. -/
theorem uniformProfile_apply_eq_prod (p : RankProfile m n) :
    uniformProfile m n p =
      (∏ i : Fin m, PMF.uniformOfFintype (Equiv.Perm (Fin n)) (p.manRank i)) *
      (∏ j : Fin n, PMF.uniformOfFintype (Equiv.Perm (Fin m)) (p.womanRank j)) := by
  simp only [uniformProfile, PMF.uniformOfFintype_apply, card, Fintype.card_perm,
    Fintype.card_fin, Finset.prod_const, Finset.card_univ, Nat.cast_mul, Nat.cast_pow]
  rw [ENNReal.mul_inv (a := (n.factorial : ENNReal) ^ m)
    (b := (m.factorial : ENNReal) ^ n) (by simp) (by simp)]
  simp [ENNReal.inv_pow]

/-- The profile law is normalized, including empty populations. -/
theorem uniformProfile_univ (m n : ℕ) :
    (uniformProfile m n).toMeasure Set.univ = 1 := by simp

/-- Choosing a full preference profile uniformly at random gives the same distribution as
choosing each agent's ranking independently and uniformly at random. -/
theorem uniformProfile_map_agentRanks (m n : ℕ) :
    (uniformProfile m n).toMeasure.map (equivAgentRanks m n) =
      Measure.pi (fun a ↦ (PMF.uniformOfFintype (Ranking m n a)).toMeasure) := by
  rw [PMF.toMeasure_map _ _ Measurable.of_discrete]
  rw [uniformProfile, PMF.map_uniformOfFintype]
  exact PMF.toMeasure_uniformOfFintype_pi (α := Ranking m n)

/-- Every agent's ranking is uniform on all permutations of the other population. -/
theorem uniformProfile_map_ranking (m n : ℕ) (a : Fin m ⊕ Fin n) :
    (uniformProfile m n).toMeasure.map (fun p ↦ equivAgentRanks m n p a) =
      (PMF.uniformOfFintype (Ranking m n a)).toMeasure := by
  calc
    _ = ((uniformProfile m n).toMeasure.map (equivAgentRanks m n)).map
        (Function.eval a) := by
      exact (Measure.map_map (measurable_pi_apply a) Measurable.of_discrete).symm
    _ = _ := by
      rw [uniformProfile_map_agentRanks]
      exact (measurePreserving_eval _ a).map_eq

theorem uniformProfile_map_manRank (i : Fin m) :
    (uniformProfile m n).toMeasure.map (fun p ↦ p.manRank i) =
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure :=
  uniformProfile_map_ranking m n (Sum.inl i)

theorem uniformProfile_map_womanRank (j : Fin n) :
    (uniformProfile m n).toMeasure.map (fun p ↦ p.womanRank j) =
      (PMF.uniformOfFintype (Equiv.Perm (Fin m))).toMeasure :=
  uniformProfile_map_ranking m n (Sum.inr j)

/-- All individual rankings are jointly independent, across as well as within the two sides. -/
theorem iIndepFun_uniformProfile (m n : ℕ) :
    ProbabilityTheory.iIndepFun (fun a p ↦ equivAgentRanks m n p a)
      (uniformProfile m n).toMeasure := by
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun _ ↦ Measurable.of_discrete.aemeasurable)).mpr
  simp only [uniformProfile_map_ranking]
  exact uniformProfile_map_agentRanks m n

/-- Independent uniform individual laws give exactly the uniform law on full profiles. -/
theorem independentProfile_uniform (m n : ℕ) :
    independentProfile (fun a ↦ PMF.uniformOfFintype (Ranking m n a)) = uniformProfile m n := by
  apply PMF.toMeasure_injective
  have h : (independentProfile (fun a ↦ PMF.uniformOfFintype (Ranking m n a))).toMeasure.map
      (equivAgentRanks m n) = (uniformProfile m n).toMeasure.map (equivAgentRanks m n) := by
    rw [independentProfile_map_agentRanks, uniformProfile_map_agentRanks]
  have h' := congrArg (Measure.map (equivAgentRanks m n).symm) h
  simpa [Measure.map_map Measurable.of_discrete Measurable.of_discrete] using h'

/-- Under the uniform specialization, expectation is the average over all full profiles. -/
theorem expectedAverageProposerRank_uniform_eq_sum
    (outcome : RankProfile m n → Fin m ≃. Fin n) :
    expectedAverageProposerRank (uniformProfile m n) outcome =
      (∑ p : RankProfile m n, (p.totalProposerRank (outcome p) : ℝ)) /
        ((Fintype.card (RankProfile m n) : ℝ) * m) := by
  rw [expectedAverageProposerRank, uniformProfile, PMF.integral_uniformOfFintype,
    Fintype.expect_eq_sum_div_card]
  simp_rw [averageProposerRank_eq_total_div]
  rw [← Finset.sum_div, div_div, mul_comm (m : ℝ)]

end RankProfile
end MathEconLib.Matching.MarriageMarket
