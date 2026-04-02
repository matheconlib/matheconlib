module

public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.Probability.Notation

/-!
Some results on probability measures.
-/

@[expose] public section

namespace MeasureTheory

open scoped ProbabilityTheory

lemma ProbabilityMeasure.measurableEmbedding_toMeasure {α : Type*}
    [MeasurableSpace α] : MeasurableEmbedding (toMeasure (Ω := α)) :=
  .subtype_coe measurableSet_isProbabilityMeasure

@[fun_prop]
lemma ProbabilityMeasure.measurable_toMeasure {α : Type*}
    [MeasurableSpace α] : Measurable (toMeasure (Ω := α)) :=
  measurableEmbedding_toMeasure.measurable

lemma ProbabilityMeasure.measurable_map {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {f : α → β} (hf : Measurable f) :
    Measurable fun μ : ProbabilityMeasure α ↦ μ.map hf.aemeasurable :=
  (Measure.measurable_map f hf).subtype_map fun μ hμ ↦
    @μ.isProbabilityMeasure_map _ _ _ _ hμ _ hf.aemeasurable

lemma ProbabilityMeasure.measurable_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] :
    Measurable (ProbabilityMeasure.pi : _ → ProbabilityMeasure ((i : ι) → α i)) := by
  rw [← measurableEmbedding_toMeasure.measurable_comp_iff]
  refine @Measurable.measure_of_isPiSystem_of_isProbabilityMeasure _ _ _ _ _
    (fun _ ↦ Subtype.property _) _ generateFrom_pi.symm isPiSystem_pi ?_
  intro t ⟨t', ht', ht''⟩
  simp only [← ht'', Function.comp_def, toMeasure_pi, Measure.pi_pi]
  refine Finset.measurable_prod _ fun i _ ↦ ?_
  exact (Measure.measurable_coe (ht' i trivial)).comp <| measurable_subtype_coe.comp <|
    measurable_pi_apply i

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

lemma ProbabilityMeasure.measurable_integral {α : Type*} [MeasurableSpace α]
    {f : α → ℝ} (hf : Measurable f) (hf' : Bornology.IsBounded (Set.range f)) :
    Measurable (fun μ : ProbabilityMeasure α ↦ μ[f]) := by
  rw [show (fun μ : ProbabilityMeasure α ↦ μ[f]) = fun μ ↦
      (∫⁻ a, .ofReal (f a) ∂μ.toMeasure).toReal - (∫⁻ a, .ofReal (-f a) ∂μ.toMeasure).toReal by
    ext μ
    have ⟨C, hC⟩ := hf'.exists_norm_le
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part <| .of_bound hf.aestronglyMeasurable
      C <| .of_forall <| by simpa using hC]]
  have : Measurable fun μ : Measure α ↦ ∫⁻ a, .ofReal (f a) ∂μ :=
    Measure.measurable_lintegral <| by fun_prop
  have : Measurable fun μ : Measure α ↦ ∫⁻ a, .ofReal (-f a) ∂μ :=
    Measure.measurable_lintegral <| by fun_prop
  fun_prop

@[simps]
noncomputable def ProbabilityMeasure.equivStdSimplex {α : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α ] [Fintype α] : ProbabilityMeasure α ≃ stdSimplex ℝ α where
  toFun μ := ⟨fun a ↦ μ {a}, by simp, by
    simp_rw [← μ.measureReal_eq_coe_coeFn, sum_measureReal_singleton]; simp⟩
  invFun x := ⟨∑ a, ENNReal.ofNNReal ⟨x a, x.2.1 a⟩ • Measure.dirac a, ⟨by
    simp [← ENNReal.toReal_eq_one_iff, ← ENNReal.coe_finset_sum]⟩⟩
  left_inv μ := by
    refine ProbabilityMeasure.toMeasure_injective <| Measure.ext_of_singleton fun a ↦ ?_
    classical
    simp [Set.indicator]
    exact μ.ennreal_coeFn_eq_coeFn_toMeasure _
  right_inv x := by
    ext a
    classical
    simp [Set.indicator]
    rfl

end MeasureTheory
