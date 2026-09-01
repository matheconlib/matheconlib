module

import Auctionlib.ValueDistribution.PostedPriceFirstOrder
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
open SingleParameterProblem

namespace ValueDistributionExamples

/-! ## Bounded continuous distribution -/

/-- The uniform distribution on `[0, 1]`, constructed by pushing the canonical
probability measure on mathlib's unit interval into `ℝ`. -/
def uniformUnitIntervalDistribution : ValueDistribution :=
  ValueDistribution.ofRandomVariable
    (⟨volume, inferInstance⟩ : ProbabilityMeasure unitInterval)
    ((↑) : unitInterval → ℝ)
    measurable_subtype_coe.aemeasurable

/-- The pushforward construction is Lebesgue measure restricted to `[0, 1]`. -/
private lemma uniformUnitIntervalDistribution_toMeasure :
    ((uniformUnitIntervalDistribution : ValueDistribution) : Measure ℝ) =
      volume.restrict (Icc 0 1) := by
  rw [uniformUnitIntervalDistribution,
    ValueDistribution.toMeasure_ofRandomVariable]
  exact unitInterval.measurePreserving_coe.map_eq

local instance :
    NoAtoms ((uniformUnitIntervalDistribution : ValueDistribution) : Measure ℝ) := by
  rw [uniformUnitIntervalDistribution_toMeasure]
  infer_instance

/-- Its values lie in `[0, 1]` almost surely. -/
private lemma uniformUnitIntervalDistribution_supported :
    uniformUnitIntervalDistribution.IsSupportedOnInterval 0 1 := by
  rw [ValueDistribution.IsSupportedOnInterval,
    uniformUnitIntervalDistribution_toMeasure]
  exact ae_restrict_mem measurableSet_Icc

/-- The uniform law is absolutely continuous with respect to Lebesgue measure. -/
private lemma uniformUnitIntervalDistribution_absolutelyContinuous :
    ((uniformUnitIntervalDistribution : ValueDistribution) : Measure ℝ) ≪
      volume := by
  rw [uniformUnitIntervalDistribution_toMeasure]
  exact Measure.absolutelyContinuous_restrict

/-- The constant function one is a density representative on `[0, 1]`. -/
private lemma uniformUnitIntervalDistribution_density_one :
    (fun _ : ℝ => (1 : ℝ)) =ᵐ[volume.restrict (Icc 0 1)]
      uniformUnitIntervalDistribution.realDensity := by
  have hrn :
      ((volume : Measure ℝ).restrict (Icc 0 1)).rnDeriv volume =ᵐ[volume]
        (Icc 0 1).indicator 1 :=
    Measure.rnDeriv_restrict_self volume measurableSet_Icc
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae hrn] with value hvalue hrnvalue
  rw [ValueDistribution.realDensity,
    uniformUnitIntervalDistribution_toMeasure, hrnvalue]
  simp [hvalue]

/-- Demand under the uniform law is the length of the remaining upper tail. -/
private lemma uniformUnitIntervalDistribution_probAtLeast
    (value : ℝ) (hvalue : value ∈ Icc 0 1) :
    uniformUnitIntervalDistribution.probAtLeast value = 1 - value := by
  rw [ValueDistribution.probAtLeast,
    ← uniformUnitIntervalDistribution.measureReal_eq_coe_coeFn,
    uniformUnitIntervalDistribution_toMeasure, Measure.real,
    Measure.restrict_apply measurableSet_Ici]
  have hset : Ici value ∩ Icc 0 1 = Icc value 1 := by
    ext point
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨hvaluePoint, _, hpointOne⟩
      exact ⟨hvaluePoint, hpointOne⟩
    · rintro ⟨hvaluePoint, hpointOne⟩
      exact ⟨hvaluePoint, hvalue.1.trans hvaluePoint, hpointOne⟩
  rw [hset, Real.volume_Icc]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr hvalue.2)

/-- On the support interval, the uniform CDF is the identity function. -/
private lemma uniformUnitIntervalDistribution_cdf
    (value : ℝ) (hvalue : value ∈ Icc 0 1) :
    ProbabilityTheory.cdf
        (uniformUnitIntervalDistribution : Measure ℝ) value = value := by
  have hdemand :=
    uniformUnitIntervalDistribution_probAtLeast value hvalue
  rw [uniformUnitIntervalDistribution.probAtLeast_eq_one_sub_cdf] at hdemand
  linarith

/-- At the interior price `1 / 2`, the uniform CDF has derivative one. -/
private lemma uniformUnitIntervalDistribution_hasDerivAt_cdf_half :
    HasDerivAt
      (ProbabilityTheory.cdf
        (uniformUnitIntervalDistribution : Measure ℝ))
      1 ((1 : ℝ) / 2) := by
  apply (hasDerivAt_id ((1 : ℝ) / 2)).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (a := (0 : ℝ)) (b := 1)
    (by norm_num) (by norm_num)] with value hvalue
  simpa only [id_eq] using
    uniformUnitIntervalDistribution_cdf value hvalue

/-- Uniform virtual-surplus weight is the affine function `2 * value - 1`. -/
private lemma uniformUnitIntervalDistribution_virtualSurplusWeight
    (value : ℝ) (hvalue : value ∈ Icc 0 1) :
    uniformUnitIntervalDistribution.virtualSurplusWeight
        (fun _ : ℝ => (1 : ℝ)) value =
      2 * value - 1 := by
  rw [ValueDistribution.virtualSurplusWeight,
    uniformUnitIntervalDistribution_probAtLeast value hvalue]
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
    exact uniformUnitIntervalDistribution_density_one
  case hD =>
    exact uniformUnitIntervalDistribution_absolutelyContinuous
  case hsupport =>
    exact uniformUnitIntervalDistribution_supported
  case hcutoff =>
    norm_num

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
    exact uniformUnitIntervalDistribution_hasDerivAt_cdf_half
  case hmax =>
    exact uniformUnitIntervalDistribution_isMaxOn_sellerProfit_half.localize
  case hdensity =>
    norm_num

/-- It is continuous in the atomless sense: no individual value has positive
probability. -/
example (price : ℝ) :
    ((uniformUnitIntervalDistribution : ValueDistribution) : Measure ℝ)
        {price} = 0 := by
  rw [uniformUnitIntervalDistribution_toMeasure,
    Measure.restrict_apply (measurableSet_singleton price)]
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
