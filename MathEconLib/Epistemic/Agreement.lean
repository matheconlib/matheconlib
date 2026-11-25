/-
Copyright (c) 2026 Ben Eltschig, Jujian Zhang, Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig, Jujian Zhang, Ruiz Chen
-/
module

public import MathEconLib.Epistemic.Posterior

/-!
# Aumann's agreement theorem

Agents have information partitions of a common state space and priors on it. An event is common
knowledge at `ω` when it contains the part of `ω` in the finest common coarsening of the agents'
partitions. Since `Setoid.Partitions` is ordered by refinement, that coarsening is the supremum
`P₁ ⊔ P₂`, or `⨆ i, P i` for a family of agents.

Aumann's theorem says that agents with a common prior cannot agree to disagree: if their
posteriors of an event are common knowledge, the posteriors are equal. The statements here allow
each agent a separate prior and assume instead that the priors give the same posterior to the
common-knowledge partition at `ω`. The common-prior statements follow because that assumption
then holds by definition.

All partitions are measurable with parts of positive prior probability; such partitions are
countable. The priors need only be finite measures, and the event must be measurable.

## Main statements

* `MathEconLib.Epistemic.aumann_agreement`: the two-agent modular agreement theorem
  (Chen et al., Theorem 3.1).
* `MathEconLib.Epistemic.aumann_agreement_of_commonPrior`: the two-agent common-prior
  specialization (Corollary 3.2).
* `MathEconLib.Epistemic.aumann_agreement_iSup`: the indexed extension in Appendix A.
* `MathEconLib.Epistemic.aumann_agreement_iSup_of_commonPrior`: its common-prior specialization.

## References

Robert J. Aumann (1976), *Agreeing to Disagree*, *The Annals of Statistics* **4**(6),
1236–1239. [DOI: 10.1214/aos/1176343654](https://doi.org/10.1214/aos/1176343654).

Ruize Chen, Ben Eltschig, Scott Duke Kominers, Ken Ono, and Jujian Zhang (2026),
*We Can't Agree to Disagree, Formally: Aumann's Theorem and Assumption Accounting in Lean*,
Theorem 3.1, Corollary 3.2, and Appendix A.
[DOI: 10.2139/ssrn.6837298](https://doi.org/10.2139/ssrn.6837298).

## Provenance

Ported from the `AgreeToDisagree` Lean development
(<https://github.com/AxiomMath/AgreeToDisagree>), file `AgreeToDisagree/AgreeToDisagree.lean`,
Copyright (c) 2026 Axiom Math, released under the MIT License; its notice is reproduced in
`docs/licenses/AgreeToDisagree-MIT.txt`. `aumann_agreement_of_commonPrior` is the statement
posed in that development's `input/AgreeToDisagree.lean`, without its hypothesis that `P₁ ⊔ P₂`
is measurable, which the proof does not use; `aumann_agreement_iSup_of_commonPrior` is new.
-/

@[expose] public section

open MeasureTheory Setoid
open scoped ENNReal

namespace MathEconLib.Epistemic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Aumann's agreement theorem** for two agents. Let `P₁` and `P₂` be measurable information
partitions whose parts have positive probability under the agents' priors `μ₁` and `μ₂`, and let
`E` be a measurable event. Suppose it is common knowledge at `ω` that the first agent's posterior
of `E` is `p₁` and the second agent's is `p₂`, and that the two priors give `E` the same
posterior on the common-knowledge partition `P₁ ⊔ P₂` at `ω`. Then `p₁ = p₂`. -/
theorem aumann_agreement {P₁ P₂ : Partitions Ω} {μ₁ μ₂ : Measure Ω} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] (hP₁ : P₁.Measurable) (hP₂ : P₂.Measurable)
    (hP₁' : ∀ s ∈ P₁, 0 < μ₁ s) (hP₂' : ∀ s ∈ P₂, 0 < μ₂ s)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p₁ p₂ : ℝ≥0∞}
    (h : (P₁ ⊔ P₂).partOf ω ⊆ {ω' | posterior P₁ μ₁ E ω' = p₁ ∧ posterior P₂ μ₂ E ω' = p₂})
    (h' : posterior (P₁ ⊔ P₂) μ₁ E ω = posterior (P₁ ⊔ P₂) μ₂ E ω) :
    p₁ = p₂ := by
  rw [← posterior_eq_of_le hP₁ hP₁' le_sup_left hE ω fun _ hω' ↦ (h hω').1,
    ← posterior_eq_of_le hP₂ hP₂' le_sup_right hE ω fun _ hω' ↦ (h hω').2]
  exact h'

/-- **Aumann's agreement theorem** for a family of agents indexed by `ι`. If every agent's
posterior of a measurable event `E` is common knowledge at `ω`, and all priors give `E` the same
posterior on the common-knowledge partition `⨆ i, P i` at `ω`, then all posteriors agree. -/
theorem aumann_agreement_iSup {ι : Type*} {μ : ι → Measure Ω} [∀ i, IsFiniteMeasure (μ i)]
    {P : ι → Partitions Ω} (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, 0 < μ i s)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ι → ℝ≥0∞}
    (h : (⨆ i, P i).partOf ω ⊆ {ω' | ∀ i, posterior (P i) (μ i) E ω' = p i})
    (h' : ∀ i j, posterior (⨆ i, P i) (μ i) E ω = posterior (⨆ i, P i) (μ j) E ω) :
    ∀ i j, p i = p j := by
  intro i j
  rw [← posterior_eq_of_le (hP i) (hP' i) (le_iSup P i) hE ω fun _ hω' ↦ h hω' i,
    ← posterior_eq_of_le (hP j) (hP' j) (le_iSup P j) hE ω fun _ hω' ↦ h hω' j]
  exact h' i j

/-- **Aumann's agreement theorem** with a common prior: two agents whose posteriors of a
measurable event are common knowledge at `ω` have equal posteriors. -/
theorem aumann_agreement_of_commonPrior {P₁ P₂ : Partitions Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hP₁ : P₁.Measurable) (hP₂ : P₂.Measurable)
    (hP₁' : ∀ s ∈ P₁, 0 < μ s) (hP₂' : ∀ s ∈ P₂, 0 < μ s)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p₁ p₂ : ℝ≥0∞}
    (h : (P₁ ⊔ P₂).partOf ω ⊆ {ω' | posterior P₁ μ E ω' = p₁ ∧ posterior P₂ μ E ω' = p₂}) :
    p₁ = p₂ :=
  aumann_agreement hP₁ hP₂ hP₁' hP₂' hE ω h rfl

/-- **Aumann's agreement theorem** with a common prior for a family of agents: if all
posteriors of a measurable event are common knowledge at `ω`, they are equal. -/
theorem aumann_agreement_iSup_of_commonPrior {ι : Type*} {μ : Measure Ω} [IsFiniteMeasure μ]
    {P : ι → Partitions Ω} (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, 0 < μ s)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ι → ℝ≥0∞}
    (h : (⨆ i, P i).partOf ω ⊆ {ω' | ∀ i, posterior (P i) μ E ω' = p i}) :
    ∀ i j, p i = p j :=
  aumann_agreement_iSup (μ := fun _ ↦ μ) hP hP' hE ω h fun _ _ ↦ rfl

end MathEconLib.Epistemic
