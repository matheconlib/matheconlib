/-
Copyright (c) 2026 Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen
-/
module

import MathEconLib.Epistemic

/-!
# API pins for the epistemic layer

These compile-time clients import only the public umbrella. The first sections pin the exact
statements of the public API, including its finite-prior and s-finite hypotheses, so that
strengthening a hypothesis breaks the build. The last section restates the theorems in the form
of the `AgreeToDisagree` development they are ported from, with probability-measure priors and
`μ s > 0` hypotheses, and derives each from the library statement.
-/

-- This module only contains anonymous compile-time clients.
set_option linter.privateModule false

open MeasureTheory Setoid MathEconLib.Epistemic
open scoped ENNReal ProbabilityTheory

variable {α Ω ι : Type*} [MeasurableSpace Ω]

/-! ## Partitions -/

example {P Q : Partitions α} : P ≤ Q ↔ ∀ s ∈ P, ∃ t ∈ Q, s ⊆ t :=
  Partitions.le_iff_forall_exists_subset

example (P : Partitions α) (a : α) : a ∈ P.partOf a ∧ P.partOf a ∈ P :=
  ⟨P.mem_partOf_self a, P.partOf_mem a⟩

example {P : Partitions α} {s : Set α} {a : α} (hs : s ∈ P) (ha : a ∈ s) : P.partOf a = s :=
  Partitions.partOf_eq_of_mem hs ha

example (r : Setoid α) (a : α) : (Partition.orderIso α r).partOf a = {b | r b a} :=
  Partitions.partOf_orderIso r a

example {P Q : Partitions α} (h : P ≤ Q) (a : α) :
    Q.partOf a = ⋃ s ∈ {s ∈ P | s ⊆ Q.partOf a}, s :=
  Partitions.partOf_eq_biUnion_of_le h a

example {P Q : Partitions Ω} (hP : P.Measurable) (hc : (P : Set (Set Ω)).Countable)
    (h : P ≤ Q) : Q.Measurable :=
  hP.mono hc h

example {P Q : Partitions Ω} (hP : P.Measurable) (hQ : Q.Measurable)
    (h : (P : Set (Set Ω)).Countable ∨ (Q : Set (Set Ω)).Countable) : (P ⊔ Q).Measurable :=
  hP.sup hQ h

example {μ : Measure Ω} [SFinite μ] {P : Partitions Ω} (hP : P.Measurable)
    (hpos : ∀ s ∈ P, 0 < μ s) : (P : Set (Set Ω)).Countable :=
  Partitions.countable_of_measure_pos hP hpos

example (μ : Measure Ω) {P : Partitions Ω} (hP : P.Measurable)
    (hc : (P : Set (Set Ω)).Countable) {A : Set Ω} (hA : MeasurableSet A) :
    μ A = ∑' s : P, μ (A ∩ s) :=
  Partitions.measure_eq_tsum_inter μ hP hc hA

/-! ## Posteriors and agreement -/

example (P : Partitions Ω) (μ : Measure Ω) (E : Set Ω) (ω : Ω) :
    posterior P μ E ω = μ (E ∩ P.partOf ω) / μ (P.partOf ω) :=
  rfl

example {P : Partitions Ω} {μ : Measure Ω} {E : Set Ω} {ω : Ω}
    (h : MeasurableSet (P.partOf ω)) : posterior P μ E ω = μ[E | P.partOf ω] :=
  posterior_eq_cond h

example {μ : Measure Ω} [IsFiniteMeasure μ] {P Q : Partitions Ω} (hP : P.Measurable)
    (hP' : ∀ s ∈ P, 0 < μ s) (hQ : P ≤ Q) {E : Set Ω} (hE : MeasurableSet E) (ω : Ω)
    {q : ℝ≥0∞} (h : ∀ ω' ∈ Q.partOf ω, posterior P μ E ω' = q) :
    posterior Q μ E ω = q :=
  posterior_eq_of_le hP hP' hQ hE ω h

example {μ₁ μ₂ : Measure Ω} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {P₁ P₂ : Partitions Ω} (hP₁ : P₁.Measurable) (hP₂ : P₂.Measurable)
    (hP₁' : ∀ s ∈ P₁, 0 < μ₁ s) (hP₂' : ∀ s ∈ P₂, 0 < μ₂ s)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p₁ p₂ : ℝ≥0∞}
    (h : (P₁ ⊔ P₂).partOf ω ⊆ {ω' | posterior P₁ μ₁ E ω' = p₁ ∧ posterior P₂ μ₂ E ω' = p₂})
    (h' : posterior (P₁ ⊔ P₂) μ₁ E ω = posterior (P₁ ⊔ P₂) μ₂ E ω) :
    p₁ = p₂ :=
  aumann_agreement hP₁ hP₂ hP₁' hP₂' hE ω h h'

example {μ : ι → Measure Ω} [∀ i, IsFiniteMeasure (μ i)] {P : ι → Partitions Ω}
    (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, 0 < μ i s)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ι → ℝ≥0∞}
    (h : (⨆ i, P i).partOf ω ⊆ {ω' | ∀ i, posterior (P i) (μ i) E ω' = p i})
    (h' : ∀ i j, posterior (⨆ i, P i) (μ i) E ω = posterior (⨆ i, P i) (μ j) E ω) :
    ∀ i j, p i = p j :=
  aumann_agreement_iSup hP hP' hE ω h h'

example {μ : Measure Ω} [IsFiniteMeasure μ] {P₁ P₂ : Partitions Ω} (hP₁ : P₁.Measurable)
    (hP₂ : P₂.Measurable) (hP₁' : ∀ s ∈ P₁, 0 < μ s) (hP₂' : ∀ s ∈ P₂, 0 < μ s)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p₁ p₂ : ℝ≥0∞}
    (h : (P₁ ⊔ P₂).partOf ω ⊆ {ω' | posterior P₁ μ E ω' = p₁ ∧ posterior P₂ μ E ω' = p₂}) :
    p₁ = p₂ :=
  aumann_agreement_of_commonPrior hP₁ hP₂ hP₁' hP₂' hE ω h

example {μ : Measure Ω} [IsFiniteMeasure μ] {P : ι → Partitions Ω}
    (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, 0 < μ s)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ι → ℝ≥0∞}
    (h : (⨆ i, P i).partOf ω ⊆ {ω' | ∀ i, posterior (P i) μ E ω' = p i}) :
    ∀ i j, p i = p j :=
  aumann_agreement_iSup_of_commonPrior hP hP' hE ω h

/-! ## Common `p`-belief -/

example {P : Partitions Ω} {μ : Measure Ω} {p : ℝ≥0∞} {E : Set Ω} :
    IsEvidentBelief P μ p E ↔ E ⊆ {ω | p ≤ posterior P μ E ω} :=
  isEvidentBelief_iff

example {P : ι → Partitions Ω} {μ : Measure Ω} {p : ℝ≥0∞} {C : Set Ω} {ω : Ω} :
    IsCommonBeliefAt P μ p C ω ↔
      ∃ E : Set Ω, ω ∈ E ∧ (∀ i, IsEvidentBelief (P i) μ p E) ∧ ∀ i, E ⊆ belief (P i) μ p C :=
  isCommonBeliefAt_iff

example {P : Partitions Ω} (hP : P.Measurable) (hPc : (P : Set (Set Ω)).Countable)
    (μ : Measure Ω) (p : ℝ≥0∞) (X : Set Ω) : MeasurableSet (belief P μ p X) :=
  measurableSet_belief hP hPc μ p X

example {P : Partitions Ω} {μ : Measure Ω} {p : ℝ≥0∞} (hp : 0 < p) (X : Set Ω) :
    belief P μ p (belief P μ p X) ⊆ belief P μ p X :=
  belief_belief_subset hp X

example {P : Partitions Ω} {μ : Measure Ω} {p r : ℝ≥0∞} {E : Set Ω} {ω : Ω} (hp : 0 < p)
    (hω : ω ∈ belief P μ p {ω' | posterior P μ E ω' = r}) : posterior P μ E ω = r :=
  posterior_eq_of_mem_belief hp hω

example {P : Partitions Ω} {μ : Measure Ω} {p : ℝ≥0∞} {A : Set Ω} {ω : Ω}
    (hA : IsEvidentBelief P μ p A) (hp : 0 < p) (hω : ω ∈ A) : 0 < μ A :=
  hA.measure_pos hp hω

example {μ : Measure Ω} [IsFiniteMeasure μ] {P : Partitions Ω} {p r : ℝ≥0∞} {A E : Set Ω}
    (hAev : IsEvidentBelief P μ p A) (hP : P.Measurable) (hP' : ∀ s ∈ P, 0 < μ s)
    (hA : MeasurableSet A) (hAmu : 0 < μ A) (hE : MeasurableSet E)
    (hAR : ∀ ω ∈ A, posterior P μ E ω = r) :
    |r.toReal - (μ (E ∩ A) / μ A).toReal| ≤ 1 - p.toReal :=
  hAev.abs_toReal_sub_le hP hP' hA hAmu hE hAR

example {μ : Measure Ω} [IsFiniteMeasure μ] {P : ι → Partitions Ω}
    (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, 0 < μ s)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ℝ≥0∞} (hp : 0 < p) {r : ι → ℝ≥0∞}
    (h : IsCommonBeliefAt P μ p {ω | ∀ i, posterior (P i) μ E ω = r i} ω) :
    ∀ i j, |(r i).toReal - (r j).toReal| ≤ 2 * (1 - p.toReal) :=
  abs_toReal_sub_le_of_isCommonBeliefAt hP hP' hE ω hp h

/-! ## Source statements

The `AgreeToDisagree` theorems assume probability-measure priors and state positivity as
`μ s > 0`. They follow from the library statements. -/

example {μ₁ μ₂ : Measure Ω} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {P₁ P₂ : Partitions Ω} (hP₁ : P₁.Measurable) (hP₂ : P₂.Measurable)
    (hP₁' : ∀ s ∈ P₁, μ₁ s > 0) (hP₂' : ∀ s ∈ P₂, μ₂ s > 0)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p₁ p₂ : ℝ≥0∞}
    (h : (P₁ ⊔ P₂).partOf ω ⊆ {ω' | posterior P₁ μ₁ E ω' = p₁ ∧ posterior P₂ μ₂ E ω' = p₂})
    (h' : posterior (P₁ ⊔ P₂) μ₁ E ω = posterior (P₁ ⊔ P₂) μ₂ E ω) :
    p₁ = p₂ :=
  aumann_agreement hP₁ hP₂ hP₁' hP₂' hE ω h h'

example {μ : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μ i)] {P : ι → Partitions Ω}
    (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, μ i s > 0)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ι → ℝ≥0∞}
    (h : (⨆ i, P i).partOf ω ⊆ {ω' | ∀ i, posterior (P i) (μ i) E ω' = p i})
    (h' : ∀ i j, posterior (⨆ i, P i) (μ i) E ω = posterior (⨆ i, P i) (μ j) E ω) :
    ∀ i j, p i = p j :=
  aumann_agreement_iSup hP hP' hE ω h h'

example {μ : Measure Ω} [IsProbabilityMeasure μ] {P : ι → Partitions Ω}
    (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, μ s > 0)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ℝ≥0∞} (hp : 0 < p) {r : ι → ℝ≥0∞}
    (h : IsCommonBeliefAt P μ p {ω | ∀ i, posterior (P i) μ E ω = r i} ω) :
    ∀ i j, |(r i).toReal - (r j).toReal| ≤ 2 * (1 - p.toReal) :=
  abs_toReal_sub_le_of_isCommonBeliefAt hP hP' hE ω hp h

#print axioms Setoid.Partitions.le_iff_forall_exists_subset
#print axioms Setoid.Partitions.partOf_eq_biUnion_of_le
#print axioms Setoid.Partitions.Measurable.sup
#print axioms Setoid.Partitions.countable_of_measure_pos
#print axioms Setoid.Partitions.measure_eq_tsum_inter
#print axioms MathEconLib.Epistemic.posterior_eq_of_le
#print axioms MathEconLib.Epistemic.aumann_agreement
#print axioms MathEconLib.Epistemic.aumann_agreement_iSup
#print axioms MathEconLib.Epistemic.aumann_agreement_of_commonPrior
#print axioms MathEconLib.Epistemic.aumann_agreement_iSup_of_commonPrior
#print axioms MathEconLib.Epistemic.belief_belief_subset
#print axioms MathEconLib.Epistemic.IsEvidentBelief.abs_toReal_sub_le
#print axioms MathEconLib.Epistemic.abs_toReal_sub_le_of_isCommonBeliefAt
