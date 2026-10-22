/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.RankPreferences
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# General finite random preference profiles

A joint law is an arbitrary `PMF (RankProfile m n)`: rankings may be correlated, and the
population sizes vary separately. `expectedAverageProposerRank` takes both the law and an
outcome rule explicitly. Choosing the existing proposer DA is an application, not an assumption
of the probability interface. `independentProfile` specializes this to arbitrary individual
ranking laws; `RandomPreferencesUniform` further specializes each ranking to the uniform law.

Directly sampling preference relations, constructing rankings sequentially, and drawing random
primitives (for example, discrete-choice shocks with a specified tie-breaking rule) are distinct
generating procedures. Each must produce a strict complete `RankProfile`; its induced joint law
is their common interface. For a discrete source use `PMF.map`, and for a general measurable
source use `Measure.map` followed by `Measure.toPMF` on this finite profile space. Equality of
induced laws implies equality of expected ranks. No equivalence of those procedures is assumed.

The profile representation and its Formal Conjectures provenance are documented in
`RankPreferences`. Stability and outcome rules reuse the existing marriage-market API.
-/

namespace MathEconLib.Matching.MarriageMarket

namespace RankProfile

variable {m n : ℕ}

/-- Discrete measurable structure on the finite profile space. -/
instance : MeasurableSpace (RankProfile m n) := ⊤

/-- Individual finite rankings carry the discrete measurable structure. -/
instance (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

instance (a : Fin m ⊕ Fin n) : MeasurableSpace (Ranking m n a) := by
  cases a <;> dsimp [Ranking] <;> infer_instance

instance (a : Fin m ⊕ Fin n) : DiscreteMeasurableSpace (Ranking m n a) := by
  cases a <;> dsimp [Ranking] <;> infer_instance

open MeasureTheory
open scoped BigOperators

/-- Expected average one-based proposer rank under any joint profile law and outcome rule.
Unmatched agents retain their outside-option ranks; the empty proposer average is zero. -/
noncomputable def expectedAverageProposerRank (μ : PMF (RankProfile m n))
    (outcome : RankProfile m n → Fin m ≃. Fin n) : ℝ :=
  ∫ p, p.averageProposerRank (outcome p) ∂μ.toMeasure

/-- For finite profiles, expectation is the sum of each profile's mass times its statistic. -/
theorem expectedAverageProposerRank_eq_sum (μ : PMF (RankProfile m n))
    (outcome : RankProfile m n → Fin m ≃. Fin n) :
    expectedAverageProposerRank μ outcome =
      ∑ p, (μ p).toReal * p.averageProposerRank (outcome p) := by
  simp [expectedAverageProposerRank, PMF.integral_eq_sum, smul_eq_mul]

/-- Different generating procedures with the same induced profile law have the same expectation. -/
theorem expectedAverageProposerRank_congr {μ ν : PMF (RankProfile m n)} (h : μ = ν)
    (outcome : RankProfile m n → Fin m ≃. Fin n) :
    expectedAverageProposerRank μ outcome = expectedAverageProposerRank ν outcome := by
  rw [h]

/-- The empty proposer average is zero for every law and outcome rule, even with receivers. -/
@[simp] theorem expectedAverageProposerRank_zero (μ : PMF (RankProfile 0 n))
    (outcome : RankProfile 0 n → Fin 0 ≃. Fin n) :
    expectedAverageProposerRank μ outcome = 0 := by
  simp [expectedAverageProposerRank, averageProposerRank]

/-- Independent, possibly nonuniform individual rankings, transported to the profile space. -/
noncomputable def independentProfile (ν : ∀ a, PMF (Ranking m n a)) : PMF (RankProfile m n) :=
  (Measure.pi (fun a ↦ (ν a).toMeasure)).toPMF.map (equivAgentRanks m n).symm

/-- The full ranking family has the product of the specified individual laws. -/
theorem independentProfile_map_agentRanks (ν : ∀ a, PMF (Ranking m n a)) :
    (independentProfile ν).toMeasure.map (equivAgentRanks m n) =
      Measure.pi (fun a ↦ (ν a).toMeasure) := by
  rw [independentProfile, ← PMF.toMeasure_map _ _ Measurable.of_discrete,
    Measure.toPMF_toMeasure, Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  simp

/-- Each coordinate has its supplied individual ranking law. -/
theorem independentProfile_map_ranking (ν : ∀ a, PMF (Ranking m n a)) (a : Fin m ⊕ Fin n) :
    (independentProfile ν).toMeasure.map (fun p ↦ equivAgentRanks m n p a) =
      (ν a).toMeasure := by
  calc
    _ = ((independentProfile ν).toMeasure.map (equivAgentRanks m n)).map
        (Function.eval a) :=
      (Measure.map_map (measurable_pi_apply a) Measurable.of_discrete).symm
    _ = _ := by
      rw [independentProfile_map_agentRanks]
      exact (measurePreserving_eval _ a).map_eq

/-- All rankings are jointly independent under the product specialization. -/
theorem iIndepFun_independentProfile (ν : ∀ a, PMF (Ranking m n a)) :
    ProbabilityTheory.iIndepFun (fun a p ↦ equivAgentRanks m n p a)
      (independentProfile ν).toMeasure := by
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun _ ↦ Measurable.of_discrete.aemeasurable)).mpr
  simp only [independentProfile_map_ranking]
  exact independentProfile_map_agentRanks ν

end RankProfile
end MathEconLib.Matching.MarriageMarket
