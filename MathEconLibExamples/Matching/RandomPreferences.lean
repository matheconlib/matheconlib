/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.RandomPreferencesUniform
import MathEconLib.Matching.Classical.Marriage.RankPreferencesDA

/-!
# Independent and correlated two-by-two proposer DA benchmarks

Under independent uniform rankings, the two proposers have different first choices with
probability `1/2`, giving average proposer rank `1`. Otherwise they share a first choice: one
gets that partner and the other gets their second choice, giving average rank `3/2`.
Thus the expectation is `(1/2) * 1 + (1/2) * (3/2) = 5/4`.

The kernel checks all sixteen profiles using the existing executable proposer DA. This samples
preference profiles and then runs DA; it does not select uniformly among stable matchings. The
benchmark concerns ordinal rank, with rank one best, rather than cardinal welfare.

The correlated example draws one uniform permutation and gives that ranking to all four agents.
Every individual ranking still has a uniform marginal, but the rankings are dependent and DA's
expected average proposer rank is `3/2`. Thus identical individual marginals need not give the
same expected outcome under different joint profile laws.

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

namespace Correlated

open MeasureTheory

/-- Every agent on both sides uses the same strict ranking table. -/
def sharedRanks (r : Equiv.Perm (Fin 2)) : RankProfile 2 2 := ⟨fun _ ↦ r, fun _ ↦ r⟩

/-- Two equally likely profiles, with all four rankings driven by one uniform permutation. -/
noncomputable def law : PMF (RankProfile 2 2) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin 2))).map sharedRanks

/-- Every individual ranking has the same uniform marginal as in the independent model. -/
theorem law_map_ranking (a : Fin 2 ⊕ Fin 2) :
    law.map (fun p ↦ equivAgentRanks 2 2 p a) =
      PMF.uniformOfFintype (Ranking 2 2 a) := by
  cases a <;> rw [law, PMF.map_comp] <;> exact PMF.map_id _

private theorem mass_identity (i : Fin 2) :
    law.toMeasure ((fun p ↦ p.manRank i) ⁻¹' ({1} : Set (Equiv.Perm (Fin 2)))) =
      (2 : ENNReal)⁻¹ := by
  rw [← Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  have hm : law.map (fun p ↦ p.manRank i) =
      PMF.uniformOfFintype (Equiv.Perm (Fin 2)) := by
    simpa using law_map_ranking (Sum.inl i)
  rw [PMF.toMeasure_map _ _ Measurable.of_discrete, hm]
  norm_num [PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply, Fintype.card_perm]

private theorem joint_mass_identity :
    law.toMeasure ((fun p ↦ p.manRank 0) ⁻¹' ({1} : Set (Equiv.Perm (Fin 2))) ∩
      (fun p ↦ p.manRank 1) ⁻¹' {1}) = (2 : ENNReal)⁻¹ := by
  rw [law, ← PMF.toMeasure_map _ _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  norm_num [Set.preimage, sharedRanks, PMF.toMeasure_apply_singleton,
    PMF.uniformOfFintype_apply, Fintype.card_perm]

/-- Uniform individual marginals do not imply that the two proposers' rankings are independent. -/
theorem not_indepFun :
    ¬ ProbabilityTheory.IndepFun (fun p : RankProfile 2 2 ↦ p.manRank 0)
      (fun p ↦ p.manRank 1) law.toMeasure := by
  intro h
  have heq := h.measure_inter_preimage_eq_mul ({1} : Set (Equiv.Perm (Fin 2))) {1}
    (measurableSet_singleton _) (measurableSet_singleton _)
  rw [joint_mass_identity, mass_identity, mass_identity] at heq
  have hreal := congrArg ENNReal.toReal heq
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv] at hreal

/-- With shared first choices, DA gives one proposer rank one and the other rank two.
The expected average is 3/2 despite the uniform marginal law of every individual ranking. -/
theorem expectedAverageProposerRank_eq_three_halves :
    expectedAverageProposerRank law (fun p ↦ p.toMarriageMarket.galeShapleyComputable) =
      (3 : ℝ) / 2 := by
  rw [expectedAverageProposerRank, law, ← PMF.toMeasure_map _ _ Measurable.of_discrete]
  rw [integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable]
  rw [PMF.integral_uniformOfFintype, Fintype.expect_eq_sum_div_card]
  simp_rw [averageProposerRank_eq_total_div]
  rw [← Finset.sum_div, ← Nat.cast_sum]
  have h : (∑ r : Equiv.Perm (Fin 2),
      (sharedRanks r).totalProposerRank (sharedRanks r).toMarriageMarket.galeShapleyComputable) =
      6 := by decide +kernel
  rw [h]
  norm_num [Fintype.card_perm]

end Correlated

end MathEconLibExamples.Matching.RandomPreferences
