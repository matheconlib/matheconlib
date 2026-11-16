/-
Copyright (c) 2026 Ben Eltschig, Jujian Zhang, Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig, Jujian Zhang, Ruiz Chen
-/
module

public import MathEconLib.ForMathlib.MeasureTheory.SetoidPartition
public import Mathlib.Probability.ConditionalProbability

/-!
# Posterior probabilities under an information partition

An agent's information is a partition `P : Setoid.Partitions Ω` of the state space: at the true
state `ω` the agent learns the part `P.part ω` and nothing more. A prior `μ` then gives the
agent's posterior probability of an event `E` at `ω`, namely `μ (E ∩ P.part ω) / μ (P.part ω)`.

`posterior` is the elementary ratio and imposes no hypotheses. On a part of measure zero it
takes the totalized value of `ℝ≥0∞` division, which is not a conditional probability; the
results in this layer assume parts of positive measure. They need only a finite prior, since
posteriors do not change when the prior is scaled.

## Main definitions

* `MathEconLib.Epistemic.posterior`: an agent's posterior probability of an event at a state.

## Main statements

* `MathEconLib.Epistemic.posterior_eq_cond`: on a measurable part, the posterior is Mathlib's
  conditional probability `μ[E | P.part ω]`.
* `MathEconLib.Epistemic.posterior_eq_of_le`: if a finer partition's posterior of `E` is `q`
  throughout a part of a coarser partition, the coarser partition's posterior there is `q`.

## Provenance

Adapted from the `AgreeToDisagree` Lean development
(<https://github.com/AxiomMath/AgreeToDisagree>), Copyright (c) 2026 Axiom Math, released under
the MIT License; its notice is reproduced in `docs/licenses/AgreeToDisagree-MIT.txt`.
-/

@[expose] public section

open MeasureTheory Set Setoid
open scoped ENNReal ProbabilityTheory

namespace MathEconLib.Epistemic

variable {Ω : Type*} [MeasurableSpace Ω] {P Q : Partitions Ω} {μ : Measure Ω}
  {E s : Set Ω} {ω : Ω}

/-- The posterior probability of the event `E` at the state `ω` for an agent with information
partition `P` and prior `μ`: the prior probability of `E` within the part of `P` containing `ω`,
relative to the probability of that part. On a null part this is the totalized `ℝ≥0∞`
division and not a conditional probability. -/
noncomputable def posterior (P : Partitions Ω) (μ : Measure Ω) (E : Set Ω) (ω : Ω) : ℝ≥0∞ :=
  μ (E ∩ P.part ω) / μ (P.part ω)

/-- The posterior at a state is computed from the part of the partition that contains it. -/
lemma posterior_eq_of_mem (hs : s ∈ P) (hω : ω ∈ s) :
    posterior P μ E ω = μ (E ∩ s) / μ s := by
  rw [posterior, Partitions.part_eq_of_mem hs hω]

/-- Two states in the same part of the partition have the same posterior. -/
lemma posterior_eq_posterior_of_mem_part {ω' : Ω} (h : ω' ∈ P.part ω) :
    posterior P μ E ω' = posterior P μ E ω := by
  rw [posterior, posterior, Partitions.mem_part_iff_part_eq_part.1 h]

/-- A larger event has a larger posterior. -/
lemma posterior_mono {F : Set Ω} (hEF : E ⊆ F) (P : Partitions Ω) (μ : Measure Ω) (ω : Ω) :
    posterior P μ E ω ≤ posterior P μ F ω :=
  ENNReal.div_le_div_right (measure_mono (inter_subset_inter_left _ hEF)) _

/-- On a measurable part, the posterior is the conditional probability given that part. -/
lemma posterior_eq_cond (h : MeasurableSet (P.part ω)) :
    posterior P μ E ω = μ[E | P.part ω] := by
  rw [posterior, ProbabilityTheory.cond_apply h, div_eq_mul_inv, mul_comm, inter_comm]

/-- Let `P` be a measurable partition into parts of positive measure, `Q` a coarser partition and
`E` a measurable event. If the `P`-posterior of `E` equals `q` at every state of `Q.part ω`, then
the `Q`-posterior of `E` at `ω` is `q`. -/
theorem posterior_eq_of_le [IsFiniteMeasure μ] (hP : P.Measurable) (hP' : ∀ s ∈ P, 0 < μ s)
    (hQ : P ≤ Q) (hE : MeasurableSet E) (ω : Ω) {q : ℝ≥0∞}
    (h : ∀ ω' ∈ Q.part ω, posterior P μ E ω' = q) :
    posterior Q μ E ω = q := by
  have hS : {s ∈ P | s ⊆ Q.part ω}.Countable :=
    (Partitions.countable_of_measure_pos hP hP').mono fun _ hs ↦ hs.1
  have hdisj : {s ∈ P | s ⊆ Q.part ω}.PairwiseDisjoint fun s ↦ s :=
    P.isPartition.pairwiseDisjoint.subset fun _ hs ↦ hs.1
  have hQω : μ (Q.part ω) ≠ 0 :=
    (pos_mono (Partitions.part_mono hQ ω) (hP' _ (P.part_mem ω))).ne'
  rw [posterior, eq_comm, ENNReal.eq_div_iff hQω (measure_ne_top _ _),
    Partitions.part_eq_biUnion_of_le hQ ω, inter_iUnion₂,
    measure_biUnion hS hdisj fun s hs ↦ hP s hs.1, ← ENNReal.tsum_mul_right,
    measure_biUnion hS ?_ fun s hs ↦ hE.inter (hP s hs.1)]
  swap
  · exact hdisj.mono' fun _ _ h ↦ h.mono inter_subset_right inter_subset_right
  refine tsum_congr fun ⟨s, hs, hsQ⟩ ↦ ?_
  obtain ⟨ω', hω'⟩ := nonempty_of_mem_partition P.isPartition hs
  rw [← h ω' (hsQ hω'), posterior_eq_of_mem hs hω', mul_comm,
    ENNReal.div_mul_cancel (hP' s hs).ne' (measure_ne_top μ s)]

end MathEconLib.Epistemic
