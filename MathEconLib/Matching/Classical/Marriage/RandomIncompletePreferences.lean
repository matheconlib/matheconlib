/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.IncompleteRankPreferences
import MathEconLib.Matching.Classical.Marriage.RandomPreferences

/-!
# Joint and independent random preferences with incomplete acceptable lists

An arbitrary `PMF (IncompleteRankProfile m n)` may correlate rankings and acceptable sets.
The independent specialization supplies one arbitrary law on optional rankings per agent;
independence neither fixes nor equates acceptable sets. Statistics include unmatched agents
at the position of their own outside option, as documented in `IncompleteRankPreferences`.

The complete profile embedding transports any existing complete law using `PMF.map`, and
the expectation bridge preserves existing complete-rank calculations for every outcome rule.
No law on outcomes or stable matchings is sampled: the outcome rule is an explicit argument.
-/

namespace MathEconLib.Matching.MarriageMarket

namespace IncompleteRankProfile

variable {m n : ℕ}

/-- The finite incomplete-profile space has the discrete measurable structure. -/
instance : MeasurableSpace (IncompleteRankProfile m n) := ⊤

/-- Optional rankings have the discrete measurable structure. -/
instance (n : ℕ) : MeasurableSpace (OptionalRanking n) := ⊤

instance (a : Fin m ⊕ Fin n) : MeasurableSpace (Ranking m n a) := by
  cases a <;> dsimp [Ranking] <;> infer_instance

instance (a : Fin m ⊕ Fin n) : DiscreteMeasurableSpace (Ranking m n a) := by
  cases a <;> dsimp [Ranking] <;> infer_instance

open MeasureTheory
open scoped BigOperators

/-- Expected average ordinal position under any joint law and explicit outcome rule. -/
noncomputable def expectedAverageProposerRank (μ : PMF (IncompleteRankProfile m n))
    (outcome : IncompleteRankProfile m n → Fin m ≃. Fin n) : ℝ :=
  ∫ p, p.averageProposerRank (outcome p) ∂μ.toMeasure

/-- Expectation is a finite weighted sum over incomplete profiles. -/
theorem expectedAverageProposerRank_eq_sum (μ : PMF (IncompleteRankProfile m n))
    (outcome : IncompleteRankProfile m n → Fin m ≃. Fin n) :
    expectedAverageProposerRank μ outcome =
      ∑ p, (μ p).toReal * p.averageProposerRank (outcome p) := by
  simp [expectedAverageProposerRank, PMF.integral_eq_sum, smul_eq_mul]

/-- Equal induced laws give equal expected ranks, regardless of the generating procedure. -/
theorem expectedAverageProposerRank_congr {μ ν : PMF (IncompleteRankProfile m n)} (h : μ = ν)
    (outcome : IncompleteRankProfile m n → Fin m ≃. Fin n) :
    expectedAverageProposerRank μ outcome = expectedAverageProposerRank ν outcome := by
  rw [h]

/-- Every law and outcome rule has zero average when the proposer population is empty. -/
@[simp] theorem expectedAverageProposerRank_zero (μ : PMF (IncompleteRankProfile 0 n))
    (outcome : IncompleteRankProfile 0 n → Fin 0 ≃. Fin n) :
    expectedAverageProposerRank μ outcome = 0 := by
  simp [expectedAverageProposerRank, averageProposerRank]

/-- Independent optional rankings, with arbitrary and possibly nonuniform individual laws. -/
noncomputable def independentProfile (ν : ∀ a, PMF (Ranking m n a)) :
    PMF (IncompleteRankProfile m n) :=
  (Measure.pi (fun a ↦ (ν a).toMeasure)).toPMF.map (equivAgentRanks m n).symm

/-- The full ranking family has the product of the supplied individual laws. -/
theorem independentProfile_map_agentRanks (ν : ∀ a, PMF (Ranking m n a)) :
    (independentProfile ν).toMeasure.map (equivAgentRanks m n) =
      Measure.pi (fun a ↦ (ν a).toMeasure) := by
  rw [independentProfile, ← PMF.toMeasure_map _ _ Measurable.of_discrete,
    Measure.toPMF_toMeasure, Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  simp

/-- Each agent's optional ranking has its supplied marginal law. -/
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

/-- The ranking coordinates, including their acceptable sets, are jointly independent. -/
theorem iIndepFun_independentProfile (ν : ∀ a, PMF (Ranking m n a)) :
    ProbabilityTheory.iIndepFun (fun a p ↦ equivAgentRanks m n p a)
      (independentProfile ν).toMeasure := by
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun _ ↦ Measurable.of_discrete.aemeasurable)).mpr
  simp only [independentProfile_map_ranking]
  exact independentProfile_map_agentRanks ν

end IncompleteRankProfile

namespace RankProfile

open MeasureTheory

variable {m n : ℕ}

/-- Transport a complete joint law explicitly to profiles with the outside option last. -/
noncomputable def toIncompleteLaw (μ : PMF (RankProfile m n)) :
    PMF (IncompleteRankProfile m n) := μ.map toIncomplete

/-- Embed one agent's complete ranking while preserving the dependent population index. -/
def rankingToIncomplete (a : Fin m ⊕ Fin n) : Ranking m n a →
    IncompleteRankProfile.Ranking m n a := by
  cases a <;> exact OptionalRanking.ofComplete

/-- Embedding a profile is the coordinatewise embedding of its individual rankings. -/
@[simp] theorem toIncomplete_equivAgentRanks (p : RankProfile m n) (a : Fin m ⊕ Fin n) :
    IncompleteRankProfile.equivAgentRanks m n p.toIncomplete a =
      rankingToIncomplete a (equivAgentRanks m n p a) := by
  cases a <;> rfl

/-- Complete independent rankings induce exactly the independent laws of their embeddings. -/
theorem toIncompleteLaw_independentProfile (ν : ∀ a, PMF (Ranking m n a)) :
    toIncompleteLaw (independentProfile ν) =
      IncompleteRankProfile.independentProfile
        (fun a ↦ (ν a).map (rankingToIncomplete a)) := by
  apply PMF.toMeasure_injective
  suffices (toIncompleteLaw (independentProfile ν)).toMeasure.map
      (IncompleteRankProfile.equivAgentRanks m n) =
    (IncompleteRankProfile.independentProfile
      (fun a ↦ (ν a).map (rankingToIncomplete a))).toMeasure.map
      (IncompleteRankProfile.equivAgentRanks m n) by
    have h := congrArg (Measure.map (IncompleteRankProfile.equivAgentRanks m n).symm) this
    simpa [Measure.map_map Measurable.of_discrete Measurable.of_discrete] using h
  rw [IncompleteRankProfile.independentProfile_map_agentRanks, toIncompleteLaw,
    ← PMF.toMeasure_map _ _ Measurable.of_discrete,
    Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  have hfun : (⇑(IncompleteRankProfile.equivAgentRanks m n) ∘ toIncomplete) =
      (fun ranks a ↦ rankingToIncomplete a (ranks a)) ∘ equivAgentRanks m n := by
    funext p a
    exact toIncomplete_equivAgentRanks p a
  rw [hfun, ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    independentProfile_map_agentRanks]
  simp_rw [← PMF.toMeasure_map _ _ Measurable.of_discrete]
  exact MeasureTheory.Measure.pi_map_pi (fun _ ↦ Measurable.of_discrete.aemeasurable)

/-- Mapping any complete joint law preserves expected ranks for every compatible outcome rule.
This applies to correlated laws as well as the existing independent uniform benchmarks. -/
theorem expectedAverageProposerRank_toIncompleteLaw (μ : PMF (RankProfile m n))
    (outcome : IncompleteRankProfile m n → Fin m ≃. Fin n) :
    IncompleteRankProfile.expectedAverageProposerRank (toIncompleteLaw μ) outcome =
      expectedAverageProposerRank μ (fun p ↦ outcome p.toIncomplete) := by
  rw [IncompleteRankProfile.expectedAverageProposerRank, toIncompleteLaw,
    ← PMF.toMeasure_map _ _ Measurable.of_discrete]
  rw [integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable]
  simp only [toIncomplete_averageProposerRank, expectedAverageProposerRank]

end RankProfile
end MathEconLib.Matching.MarriageMarket
