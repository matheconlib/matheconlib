module

import Auctionlib.ValueDistribution.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.UniformOn

/-!
# Representative Value Distributions

This file checks that the measure-first `ValueDistribution` interface can be
instantiated by standard distribution classes without adding parallel
probability constructions to the production library.
-/

noncomputable section

open scoped unitInterval

open MeasureTheory Set

namespace ValueDistributionExamples

/-! ## Bounded continuous distribution -/

/-- The uniform distribution on `[0, 1]`, constructed by pushing the canonical
probability measure on mathlib's unit interval into `ℝ`. -/
def uniformUnitIntervalDistribution : ValueDistribution :=
  ValueDistribution.ofRandomVariable
    (⟨volume, inferInstance⟩ : ProbabilityMeasure unitInterval)
    ((↑) : unitInterval → ℝ)
    measurable_subtype_coe.aemeasurable

/-- The construction uses the ordinary pushforward measure. -/
example :
    ((uniformUnitIntervalDistribution : ValueDistribution) : Measure ℝ) =
      Measure.map ((↑) : unitInterval → ℝ) volume := by
  simp [uniformUnitIntervalDistribution]

/-- Its values lie in `[0, 1]` almost surely. -/
example :
    uniformUnitIntervalDistribution.IsSupportedOnInterval 0 1 := by
  rw [ValueDistribution.IsSupportedOnInterval,
    uniformUnitIntervalDistribution,
    ValueDistribution.toMeasure_ofRandomVariable]
  apply (ae_map_iff
    (p := fun value : ℝ => value ∈ Icc 0 1)
    measurable_subtype_coe.aemeasurable measurableSet_Icc).2
  exact ae_of_all volume fun value => value.property

/-- It is continuous in the atomless sense: no individual value has positive
probability. -/
example (price : ℝ) :
    ((uniformUnitIntervalDistribution : ValueDistribution) : Measure ℝ)
        {price} = 0 := by
  rw [uniformUnitIntervalDistribution,
    ValueDistribution.toMeasure_ofRandomVariable]
  rw [Measure.map_apply_of_aemeasurable
    measurable_subtype_coe.aemeasurable (measurableSet_singleton price)]
  simp
  exact measure_mono_null inter_subset_left (measure_singleton price)

/-! ## Finite-support distribution -/

/-- The uniform distribution on the two values `0` and `1`, constructed from
the uniform probability measure on `Bool`. -/
def twoPointDistribution : ValueDistribution :=
  ValueDistribution.ofRandomVariable
    (⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩ :
      ProbabilityMeasure Bool)
    (fun selected => if selected then 1 else 0)
    (measurable_of_finite fun selected : Bool =>
      if selected then (1 : ℝ) else 0).aemeasurable

/-- Its support is contained in the finite set `{0, 1}`. -/
example :
    ∀ᵐ value ∂(twoPointDistribution : Measure ℝ),
      value ∈ ({0, 1} : Set ℝ) := by
  rw [twoPointDistribution,
    ValueDistribution.toMeasure_ofRandomVariable]
  apply (ae_map_iff
    (p := fun value : ℝ => value ∈ ({0, 1} : Set ℝ))
    (measurable_of_finite fun selected : Bool =>
      if selected then (1 : ℝ) else 0).aemeasurable
    ((measurableSet_singleton (1 : ℝ)).insert 0)).2
  exact ae_of_all _ fun selected => by cases selected <;> simp

/-! ## Unbounded distribution -/

/-- The standard Cauchy distribution, a standard unbounded real-valued
probability distribution supplied by mathlib. -/
def standardCauchyDistribution : ValueDistribution :=
  ⟨Probability.cauchyMeasure 0 1, inferInstance⟩

/-- The transparent `ValueDistribution` abbreviation leaves the underlying
mathlib measure unchanged. -/
example :
    (standardCauchyDistribution : Measure ℝ) =
      Probability.cauchyMeasure 0 1 :=
  rfl

end ValueDistributionExamples

end
