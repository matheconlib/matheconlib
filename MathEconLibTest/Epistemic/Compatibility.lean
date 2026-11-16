/-
Copyright (c) 2026 Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen
-/
module

import MathEconLib.Epistemic

/-!
# API pins for the epistemic layer

These compile-time clients import only the public umbrella. They pin the statements of the main
theorems and of the general partition API in `ForMathlib`. The agreement theorems are restated
with probability-measure priors and `μ s > 0` hypotheses, the form of the `AgreeToDisagree`
development they are ported from, and are derived from the library statements, which assume only
finite priors.
-/

-- This module only contains anonymous compile-time clients.
set_option linter.privateModule false

open MeasureTheory Setoid MathEconLib.Epistemic
open scoped ENNReal ProbabilityTheory

variable {α Ω ι : Type*} [MeasurableSpace Ω]

/-! ## Partitions -/

example {P Q : Partitions α} : P ≤ Q ↔ ∀ s ∈ P, ∃ t ∈ Q, s ⊆ t :=
  Partitions.le_iff_forall_exists_subset

example (P : Partitions α) (a : α) : a ∈ P.part a ∧ P.part a ∈ P :=
  ⟨P.mem_part_self a, P.part_mem a⟩

example {P Q : Partitions α} (h : P ≤ Q) (a : α) :
    Q.part a = ⋃ s ∈ {s ∈ P | s ⊆ Q.part a}, s :=
  Partitions.part_eq_biUnion_of_le h a

example {P Q : Partitions Ω} (hP : P.Measurable) (hc : (P : Set (Set Ω)).Countable)
    (h : P ≤ Q) : Q.Measurable :=
  hP.mono hc h

example {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Partitions Ω} (hP : P.Measurable)
    (hP' : ∀ s ∈ P, μ s > 0) : (P : Set (Set Ω)).Countable :=
  Partitions.countable_of_measure_pos hP hP'

/-! ## Posteriors and agreement -/

example (P : Partitions Ω) (μ : Measure Ω) (E : Set Ω) (ω : Ω) :
    posterior P μ E ω = μ (E ∩ P.part ω) / μ (P.part ω) :=
  rfl

example {P : Partitions Ω} {μ : Measure Ω} {E : Set Ω} {ω : Ω}
    (h : MeasurableSet (P.part ω)) : posterior P μ E ω = μ[E | P.part ω] :=
  posterior_eq_cond h

example {μ : Measure Ω} [IsProbabilityMeasure μ] {P Q : Partitions Ω} (hP : P.Measurable)
    (hP' : ∀ s ∈ P, μ s > 0) (hQ : P ≤ Q) {E : Set Ω} (hE : MeasurableSet E) (ω : Ω)
    {p : ℝ≥0∞} (h : ∀ ω' ∈ Q.part ω, posterior P μ E ω' = p) :
    posterior Q μ E ω = p :=
  posterior_eq_of_le hP hP' hQ hE ω h

example {μ₁ μ₂ : Measure Ω} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {P₁ P₂ : Partitions Ω} (hP₁ : P₁.Measurable) (hP₂ : P₂.Measurable)
    (hP₁' : ∀ s ∈ P₁, μ₁ s > 0) (hP₂' : ∀ s ∈ P₂, μ₂ s > 0)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p₁ p₂ : ℝ≥0∞}
    (h : (P₁ ⊔ P₂).part ω ⊆ {ω' | posterior P₁ μ₁ E ω' = p₁ ∧ posterior P₂ μ₂ E ω' = p₂})
    (h' : posterior (P₁ ⊔ P₂) μ₁ E ω = posterior (P₁ ⊔ P₂) μ₂ E ω) :
    p₁ = p₂ :=
  aumann_agreement hP₁ hP₂ hP₁' hP₂' hE ω h h'

example {μ : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μ i)] {P : ι → Partitions Ω}
    (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, μ i s > 0)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ι → ℝ≥0∞}
    (h : (⨆ i, P i).part ω ⊆ {ω' | ∀ i, posterior (P i) (μ i) E ω' = p i})
    (h' : ∀ i j, posterior (⨆ i, P i) (μ i) E ω = posterior (⨆ i, P i) (μ j) E ω) :
    ∀ i j, p i = p j :=
  aumann_agreement_iSup hP hP' hE ω h h'

example {μ : Measure Ω} [IsFiniteMeasure μ] {P₁ P₂ : Partitions Ω} (hP₁ : P₁.Measurable)
    (hP₂ : P₂.Measurable) (hP₁' : ∀ s ∈ P₁, 0 < μ s) (hP₂' : ∀ s ∈ P₂, 0 < μ s)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p₁ p₂ : ℝ≥0∞}
    (h : (P₁ ⊔ P₂).part ω ⊆ {ω' | posterior P₁ μ E ω' = p₁ ∧ posterior P₂ μ E ω' = p₂}) :
    p₁ = p₂ :=
  aumann_agreement_of_commonPrior hP₁ hP₂ hP₁' hP₂' hE ω h

/-! ## Common `p`-belief -/

example {P : ι → Partitions Ω} {μ : Measure Ω} {p : ℝ≥0∞} {C : Set Ω} {ω : Ω} :
    IsCommonBeliefAt P μ p C ω ↔
      ∃ E : Set Ω, ω ∈ E ∧ (∀ i, E ⊆ belief (P i) μ p E) ∧ ∀ i, E ⊆ belief (P i) μ p C :=
  Iff.rfl

example {P : Partitions Ω} {μ : Measure Ω} {p : ℝ≥0∞} (hp : 0 < p) (X : Set Ω) :
    belief P μ p (belief P μ p X) ⊆ belief P μ p X :=
  belief_belief_subset hp X

example {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Partitions Ω} (hP : P.Measurable)
    (hP' : ∀ s ∈ P, μ s > 0) {p : ℝ≥0∞} {A E : Set Ω} (hA : MeasurableSet A) (hAmu : 0 < μ A)
    (hAev : A ⊆ belief P μ p A) (hE : MeasurableSet E) {r : ℝ≥0∞}
    (hAR : ∀ ω ∈ A, posterior P μ E ω = r) :
    |r.toReal - (μ (E ∩ A) / μ A).toReal| ≤ 1 - p.toReal :=
  IsEvidentBelief.abs_toReal_sub_le hAev hP hP' hA hAmu hE hAR

example {μ : Measure Ω} [IsProbabilityMeasure μ] {P : ι → Partitions Ω}
    (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, μ s > 0)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ℝ≥0∞} (hp : 0 < p) {r : ι → ℝ≥0∞}
    (h : IsCommonBeliefAt P μ p {ω | ∀ i, posterior (P i) μ E ω = r i} ω) :
    ∀ i j, |(r i).toReal - (r j).toReal| ≤ 2 * (1 - p.toReal) :=
  abs_sub_le_of_isCommonBeliefAt hP hP' hE ω hp h

#print axioms Setoid.Partitions.le_iff_forall_exists_subset
#print axioms Setoid.Partitions.part_eq_biUnion_of_le
#print axioms Setoid.Partitions.countable_of_measure_pos
#print axioms Setoid.Partitions.measure_eq_tsum_inter
#print axioms MathEconLib.Epistemic.posterior_eq_of_le
#print axioms MathEconLib.Epistemic.aumann_agreement
#print axioms MathEconLib.Epistemic.aumann_agreement_iSup
#print axioms MathEconLib.Epistemic.aumann_agreement_of_commonPrior
#print axioms MathEconLib.Epistemic.aumann_agreement_iSup_of_commonPrior
#print axioms MathEconLib.Epistemic.IsEvidentBelief.abs_toReal_sub_le
#print axioms MathEconLib.Epistemic.abs_sub_le_of_isCommonBeliefAt
