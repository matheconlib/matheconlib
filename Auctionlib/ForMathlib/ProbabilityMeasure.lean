module

public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
Some results on probability measures.
-/

@[expose] public section

namespace MeasureTheory

lemma ProbabilityMeasure.measurableEmbedding_toMeasure {α : Type*}
    [MeasurableSpace α] : MeasurableEmbedding (toMeasure (Ω := α)) :=
  .subtype_coe measurableSet_isProbabilityMeasure

lemma ProbabilityMeasure.measurable_map {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {f : α → β} (hf : Measurable f) :
    Measurable fun μ : ProbabilityMeasure α ↦ μ.map hf.aemeasurable :=
  (Measure.measurable_map f hf).subtype_map fun μ hμ ↦
    @μ.isProbabilityMeasure_map _ _ _ _ hμ _ hf.aemeasurable

lemma ProbabilityMeasure.measurable_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] :
    Measurable (ProbabilityMeasure.pi : _ → ProbabilityMeasure ((i : ι) → α i)) := by
  rw [← measurableEmbedding_toMeasure.measurable_comp_iff]
  unfold Measure.instMeasurableSpace
  simp_rw [measurable_iff_comap_le, MeasurableSpace.comap_iSup,
    iSup₂_le_iff, MeasurableSpace.comap_comp, ← measurable_iff_comap_le]
  intro s hs
  refine MeasurableSpace.induction_on_inter (C := fun s hs ↦ Measurable
    ((fun μ ↦ μ s) ∘ toMeasure ∘ pi))
      generateFrom_pi.symm isPiSystem_pi ?_ ?_ ?_ ?_ s hs
  · simp only [measure_empty]; exact measurable_const
  · intro t ⟨t', ht', ht''⟩
    simp only [← ht'', Function.comp_def, toMeasure_pi, Measure.pi_pi]
    refine Finset.measurable_prod _ fun i _ ↦ ?_
    exact (Measure.measurable_coe (ht' i trivial)).comp <| measurable_subtype_coe.comp <|
      measurable_pi_apply i
  · intro t ht ht'
    convert ht'.const_sub 1 using 2
    rw [Function.comp_apply, measure_compl ht] <;> simp
  · intro t ht ht' ht''
    convert Measurable.ennreal_tsum ht'' using 2
    simp [measure_iUnion ht ht']

/-- The probability measure `μ.join : ProbabilityMeasure α` corresponding to a probability measure
`μ : ProbabilityMeasure (ProbabilityMeasure α)` on the space of probability measures on `α`.

This operation is part of the Giry monad. -/
@[simps]
noncomputable def ProbabilityMeasure.join {α : Type*} [MeasurableSpace α]
    (μ : ProbabilityMeasure (ProbabilityMeasure α)) : ProbabilityMeasure α where
  val := (μ.toMeasure.map (↑)).join
  property := @isProbabilityMeasure_join _ _ _
    (Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable) <|
      (ae_map_iff measurable_subtype_coe.aemeasurable
        measurableSet_isProbabilityMeasure).2 <| .of_forall fun x ↦ x.2

lemma ProbabilityMeasure.measurable_join {α : Type*} [MeasurableSpace α] :
    Measurable (join (α := α)) := by
  rw [← measurableEmbedding_toMeasure.measurable_comp_iff]
  dsimp [Function.comp_def, join]
  exact Measure.measurable_join.comp <| (Measure.measurable_map _ measurable_subtype_coe).comp
    measurable_subtype_coe

end MeasureTheory
