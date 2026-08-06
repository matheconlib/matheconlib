module

import Auctionlib.ValueDistribution.Demand
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.UniformOn

/-!
# Representative Value Distributions

This file checks that the measure-first `ValueDistribution` interface can be
instantiated by standard distribution classes without adding parallel
probability constructions to the production library. It also exercises the
demand API on finite-support atomic and unbounded atomless distributions.
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

/-- Demand at the upper support point is one half. This is a nontrivial atomic
witness: the CDF at `1` includes both support points, while `probAtLeast 1`
includes the probability mass exactly at the posted price. Thus `1 - F(1)`
would give zero without the atom term. -/
example :
    twoPointDistribution.probAtLeast 1 = (1 : ℝ) / 2 := by
  rw [ValueDistribution.probAtLeast,
    ← twoPointDistribution.measureReal_eq_coe_coeFn]
  rw [twoPointDistribution,
    ValueDistribution.toMeasure_ofRandomVariable]
  rw [Measure.real, Measure.map_apply_of_aemeasurable
    (measurable_of_finite fun selected : Bool =>
      if selected then (1 : ℝ) else 0).aemeasurable
    measurableSet_Ici]
  change (ProbabilityTheory.uniformOn (Set.univ : Set Bool)
      ((fun selected : Bool => if selected then (1 : ℝ) else 0) ⁻¹'
        Ici 1)).toReal = (1 : ℝ) / 2
  have hpreimage :
      ((fun selected : Bool => if selected then (1 : ℝ) else 0) ⁻¹'
        Ici 1) = {true} := by
    ext selected
    cases selected <;> simp
  rw [hpreimage, ProbabilityTheory.uniformOn_univ]
  norm_num

/-! ## Unbounded distribution -/

/-- The standard Cauchy distribution, a standard unbounded real-valued
probability distribution supplied by mathlib. -/
def standardCauchyDistribution : ValueDistribution :=
  ⟨Probability.cauchyMeasure 0 1, inferInstance⟩

/-- The standard Cauchy distribution is atomless because its nonzero-scale
measure has a density with respect to atomless Lebesgue measure. -/
local instance :
    NoAtoms (standardCauchyDistribution : Measure ℝ) := by
  change NoAtoms (Probability.cauchyMeasure 0 1)
  rw [Probability.cauchyMeasure_of_scale_ne_zero 0 (by norm_num)]
  infer_instance

/-- The transparent `ValueDistribution` abbreviation leaves the underlying
mathlib measure unchanged. -/
example :
    (standardCauchyDistribution : Measure ℝ) =
      Probability.cauchyMeasure 0 1 :=
  rfl

/-- The reusable atomless identity applies even without bounded support. -/
example (price : ℝ) :
    standardCauchyDistribution.probAtLeast price =
      1 - ProbabilityTheory.cdf
        (standardCauchyDistribution : Measure ℝ) price :=
  standardCauchyDistribution.probAtLeast_eq_one_sub_cdf price

/-- Demand remains between zero and one without bounded support: unbounded
values do not make the probability of an event exceed one. -/
example (price : ℝ) :
    0 ≤ standardCauchyDistribution.probAtLeast price ∧
      standardCauchyDistribution.probAtLeast price ≤ 1 :=
  ⟨standardCauchyDistribution.probAtLeast_nonneg price,
    standardCauchyDistribution.probAtLeast_le_one price⟩

end ValueDistributionExamples

end
