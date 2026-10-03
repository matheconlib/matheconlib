module

import Auctionlib.ValueDistribution
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

open MeasureTheory Set
open SingleParameterProblem
open ValueDistribution

namespace ValueDistributionExamples

/-! ## Bounded continuous distribution -/

/-- The uniform law on `[0, 1]`, as a specialization of the reusable
interval-uniform family. -/
def uniformUnitIntervalDistribution : ValueDistribution :=
  ValueDistribution.uniformInterval 0 1 (by norm_num)

/-- The family specializes to the same restricted Lebesgue measure used in
the original unit-interval example. -/
example :
    ((uniformUnitIntervalDistribution : ValueDistribution) : Measure ℝ) =
      volume.restrict (Icc 0 1) := by
  rw [uniformUnitIntervalDistribution, ValueDistribution.toMeasure_uniformInterval,
    ProbabilityTheory.cond, Real.volume_Icc]
  norm_num

local instance :
    NoAtoms ((uniformUnitIntervalDistribution : ValueDistribution) : Measure ℝ) := by
  unfold uniformUnitIntervalDistribution
  infer_instance

/-- Uniform virtual-surplus weight is the affine function `2 * value - 1`. -/
private lemma uniformUnitIntervalDistribution_virtualSurplusWeight
    (value : ℝ) (hvalue : value ∈ Icc 0 1) :
    uniformUnitIntervalDistribution.virtualSurplusWeight
        (fun _ : ℝ => (1 : ℝ)) value =
      2 * value - 1 := by
  rw [ValueDistribution.virtualSurplusWeight,
    show uniformUnitIntervalDistribution.probAtLeast value = (1 - value) by
      simpa [uniformUnitIntervalDistribution] using
        (ValueDistribution.uniformInterval_probAtLeast 0 1 (by norm_num) value hvalue)]
  ring

/-- Uniform virtual-surplus weight is nonpositive below one half. -/
private lemma uniformUnitIntervalDistribution_virtualSurplusWeight_nonpos :
    ∀ᵐ value ∂volume.restrict (Icc 0 ((1 : ℝ) / 2)),
      uniformUnitIntervalDistribution.virtualSurplusWeight
        (fun _ : ℝ => (1 : ℝ)) value ≤ 0 := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with value hvalue
  have hvalueUnit : value ∈ Icc 0 1 := by
    constructor
    · exact hvalue.1
    · exact hvalue.2.trans (by norm_num)
  rw [uniformUnitIntervalDistribution_virtualSurplusWeight value hvalueUnit]
  linarith [hvalue.2]

/-- Uniform virtual-surplus weight is nonnegative above one half. -/
private lemma uniformUnitIntervalDistribution_virtualSurplusWeight_nonneg :
    ∀ᵐ value ∂volume.restrict (Icc ((1 : ℝ) / 2) 1),
      0 ≤ uniformUnitIntervalDistribution.virtualSurplusWeight
        (fun _ : ℝ => (1 : ℝ)) value := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with value hvalue
  have hvalueUnit : value ∈ Icc 0 1 := by
    constructor
    · exact (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans hvalue.1
    · exact hvalue.2
  rw [uniformUnitIntervalDistribution_virtualSurplusWeight value hvalueUnit]
  linarith [hvalue.1]

/-- One half globally maximizes seller profit among prices in `[0, 1]` for a
uniform buyer value, zero continuation value, and zero acquisition cost. -/
private lemma uniformUnitIntervalDistribution_isMaxOn_sellerProfit_half :
    IsMaxOn
      (fun price =>
        uniformUnitIntervalDistribution.sellerProfit
          (postedPriceProblem 0 1 price) 0 0)
      (Icc 0 1) ((1 : ℝ) / 2) := by
  apply
    ValueDistribution.isMaxOn_sellerProfit_postedPriceProblem_of_netVirtualSurplus_sign
      uniformUnitIntervalDistribution 0 1 ((1 : ℝ) / 2)
      (fun _ : ℝ => (1 : ℝ)) 0 0
  case hbelow =>
    simpa using
      uniformUnitIntervalDistribution_virtualSurplusWeight_nonpos
  case habove =>
    simpa using
      uniformUnitIntervalDistribution_virtualSurplusWeight_nonneg
  case hdensity =>
    simpa [uniformUnitIntervalDistribution] using
      (ValueDistribution.uniformInterval_density 0 1 (by norm_num))
  case hD =>
    exact ValueDistribution.uniformInterval_absolutelyContinuous 0 1 (by norm_num)
  case hsupport =>
    exact ValueDistribution.uniformInterval_supported 0 1 (by norm_num)
  case hcutoff =>
    norm_num

/-- The uniform-pricing theorem agrees with the earlier virtual-surplus
argument in the interior `r = 0` case. -/
example :
    ValueDistribution.uniformOptimalPrice 0 1 0 = (1 : ℝ) / 2 := by
  norm_num [ValueDistribution.uniformOptimalPrice]

example :
    IsMaxOn
      (fun price ↦
        uniformUnitIntervalDistribution.sellerProfit
          (postedPriceProblem 0 1 price) 0 0)
      (Icc 0 1) ((1 : ℝ) / 2) := by
  have hmax := ValueDistribution.isMaxOn_sellerProfit_uniformInterval 0 1
    (by norm_num) 0 0
  rw [show ValueDistribution.uniformOptimalPrice 0 1 0 = (1 : ℝ) / 2 by
    norm_num [ValueDistribution.uniformOptimalPrice]] at hmax
  simpa only [uniformUnitIntervalDistribution] using hmax

/-- Low continuation value makes selling at the lower endpoint optimal;
high continuation value makes retaining the object optimal. -/
example : ValueDistribution.uniformOptimalPrice 0 1 (-2) = 0 := by
  norm_num [ValueDistribution.uniformOptimalPrice]

example : ValueDistribution.uniformOptimalPrice 0 1 2 = 1 := by
  norm_num [ValueDistribution.uniformOptimalPrice]

example :
    IsMaxOn
      (fun price ↦
        uniformUnitIntervalDistribution.sellerProfit
          (postedPriceProblem 0 1 price) (-2) 3)
      (Icc 0 1) 0 := by
  have hmax := ValueDistribution.isMaxOn_sellerProfit_uniformInterval 0 1
    (by norm_num) (-2) 3
  rw [show ValueDistribution.uniformOptimalPrice 0 1 (-2) = 0 by
    norm_num [ValueDistribution.uniformOptimalPrice]] at hmax
  simpa only [uniformUnitIntervalDistribution] using hmax

example :
    IsMaxOn
      (fun price ↦
        uniformUnitIntervalDistribution.sellerProfit
          (postedPriceProblem 0 1 price) 2 3)
      (Icc 0 1) 1 := by
  have hmax := ValueDistribution.isMaxOn_sellerProfit_uniformInterval 0 1
    (by norm_num) 2 3
  rw [show ValueDistribution.uniformOptimalPrice 0 1 2 = 1 by
    norm_num [ValueDistribution.uniformOptimalPrice]] at hmax
  simpa only [uniformUnitIntervalDistribution] using hmax

/-- At the lower boundary every buyer purchases, so continuation value
does not enter the realized seller payoff. -/
example :
    uniformUnitIntervalDistribution.sellerProfit
        (postedPriceProblem 0 1 0) (-2) 3 = -3 := by
  rw [uniformUnitIntervalDistribution,
    ValueDistribution.sellerProfit_uniformInterval 0 1 (by norm_num)
      0 (-2) 3 (by norm_num)]
  norm_num

/-- At the upper boundary an atomless buyer almost surely does not purchase. -/
example :
    uniformUnitIntervalDistribution.sellerProfit
        (postedPriceProblem 0 1 1) 2 3 = -1 := by
  rw [uniformUnitIntervalDistribution,
    ValueDistribution.sellerProfit_uniformInterval 0 1 (by norm_num)
      1 2 3 (by norm_num)]
  norm_num

/-- The lower endpoint does not affect the price while both optima are interior. -/
example :
    ValueDistribution.uniformOptimalPrice (-1) 2 0 =
      ValueDistribution.uniformOptimalPrice 0 2 0 := by
  apply ValueDistribution.uniformOptimalPrice_lowerEndpoint_eq_of_interior
  all_goals norm_num

/-- Doubling the upper endpoint from two to four raises the interior price
by one, half of the endpoint change. -/
example :
    ValueDistribution.uniformOptimalPrice 0 4 0 -
      ValueDistribution.uniformOptimalPrice 0 2 0 = 1 := by
  rw [ValueDistribution.uniformOptimalPrice_upperEndpoint_sub_of_interior]
  all_goals norm_num

/-- A unit increase in continuation value raises the interior price by one half. -/
example :
    ValueDistribution.uniformOptimalPrice 0 2 1 -
      ValueDistribution.uniformOptimalPrice 0 2 0 = (1 : ℝ) / 2 := by
  rw [ValueDistribution.uniformOptimalPrice_continuationValue_sub_of_interior]
  all_goals norm_num

/-- At an interior optimum for any uniform interval, the generic first-order
theorem gives virtual value equal to continuation value. -/
example (a b continuationValue acquisitionCost : ℝ) (hab : a < b)
    (hpeak : (b + continuationValue) / 2 ∈ Ioo a b) :
    (ValueDistribution.uniformInterval a b hab).virtualValue
        (fun _ : ℝ ↦ 1 / (b - a)) ((b + continuationValue) / 2) =
      continuationValue := by
  have hmax := ValueDistribution.isMaxOn_sellerProfit_uniformInterval
    a b hab continuationValue acquisitionCost
  rw [ValueDistribution.uniformOptimalPrice_eq_peak a b continuationValue
    ⟨hpeak.1.le, hpeak.2.le⟩] at hmax
  apply
    virtualValue_eq_continuationValue_of_isLocalMaxOn_sellerProfit_postedPriceProblem
      (ValueDistribution.uniformInterval a b hab)
      a b (fun _ : ℝ ↦ 1 / (b - a)) continuationValue acquisitionCost
      ((b + continuationValue) / 2)
  case hprice =>
    exact hpeak
  case hcdf =>
    exact ValueDistribution.uniformInterval_hasDerivAt_cdf
      a b hab _ hpeak
  case hmax =>
    exact hmax.localize
  case hdensity =>
    simp [ne_of_gt (sub_pos.mpr hab)]

/-- The interior first-order condition recovers zero virtual value at the
uniform monopoly price. -/
example :
    uniformUnitIntervalDistribution.virtualValue
        (fun _ : ℝ ↦ (1 : ℝ)) ((1 : ℝ) / 2) = 0 := by
  apply
    ValueDistribution.virtualValue_eq_zero_of_isLocalMaxOn_sellerProfit_postedPriceProblem
      uniformUnitIntervalDistribution
      0 1 (fun _ : ℝ ↦ (1 : ℝ)) 0 ((1 : ℝ) / 2)
  case hprice =>
    norm_num
  case hcdf =>
    simpa [uniformUnitIntervalDistribution] using
      (ValueDistribution.uniformInterval_hasDerivAt_cdf 0 1
        (by norm_num) ((1 : ℝ) / 2) (by norm_num))
  case hmax =>
    exact uniformUnitIntervalDistribution_isMaxOn_sellerProfit_half.localize
  case hdensity =>
    norm_num

/-- It is continuous in the atomless sense: no individual value has positive
probability. -/
example (price : ℝ) :
    ((uniformUnitIntervalDistribution : ValueDistribution) : Measure ℝ)
        {price} = 0 := by
  exact measure_singleton price

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
