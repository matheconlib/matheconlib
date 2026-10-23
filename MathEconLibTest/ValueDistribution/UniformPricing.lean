/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

import MathEconLib.ValueDistribution

/-!
# Uniform Distribution and Pricing API Checks

These checks use only the value-distribution umbrella, without the auction bridge or examples.
-/

noncomputable section

open MathEconLib MeasureTheory ProbabilityTheory Set SingleParameterProblem

namespace UniformPricingCompatibility

/-! ## Uniform interval distributions -/

section UniformInterval

variable (a b : ℝ) (hab : a < b)

/-- The interval-uniform law is Mathlib's conditioned Lebesgue measure. -/
example :
    ((ValueDistribution.uniformInterval a b hab : ValueDistribution) : Measure ℝ) =
      ProbabilityTheory.cond volume (Icc a b) :=
  ValueDistribution.toMeasure_uniformInterval a b hab

/-- The constructor also satisfies Mathlib's uniform-law predicate. -/
example :
    MeasureTheory.pdf.IsUniform (id : ℝ → ℝ) (Icc a b)
      ((ValueDistribution.uniformInterval a b hab : ValueDistribution) : Measure ℝ) volume :=
  ValueDistribution.isUniform_uniformInterval a b hab

/-- Interval support is a property of the resulting distribution. -/
example :
    (ValueDistribution.uniformInterval a b hab).IsSupportedOnInterval a b :=
  ValueDistribution.uniformInterval_supported a b hab

/-- The uniform law is absolutely continuous and atomless. -/
example :
    ((ValueDistribution.uniformInterval a b hab : ValueDistribution) : Measure ℝ) ≪
      volume :=
  ValueDistribution.uniformInterval_absolutelyContinuous a b hab

example :
    NullSingletonClass ((ValueDistribution.uniformInterval a b hab : ValueDistribution) : Measure ℝ) :=
  ValueDistribution.uniformInterval_noAtoms a b hab

/-- Its density is the reciprocal of interval length, almost everywhere on
the interval. -/
example :
    (fun _ : ℝ ↦ 1 / (b - a)) =ᵐ[volume.restrict (Icc a b)]
      (ValueDistribution.uniformInterval a b hab).realDensity :=
  ValueDistribution.uniformInterval_density a b hab

/-- Uniform demand and the CDF are valid at both support endpoints. -/
example (price : ℝ) (hprice : price ∈ Icc a b) :
    (ValueDistribution.uniformInterval a b hab).probAtLeast price =
      (b - price) / (b - a) :=
  ValueDistribution.uniformInterval_probAtLeast a b hab price hprice

example (price : ℝ) (hprice : price ∈ Icc a b) :
    cdf ((ValueDistribution.uniformInterval a b hab : ValueDistribution) : Measure ℝ) price =
      (price - a) / (b - a) :=
  ValueDistribution.uniformInterval_cdf a b hab price hprice

/-- The pointwise CDF derivative is asserted only in the interior. -/
example (price : ℝ) (hprice : price ∈ Ioo a b) :
    HasDerivAt
      (cdf ((ValueDistribution.uniformInterval a b hab : ValueDistribution) : Measure ℝ))
      (1 / (b - a)) price :=
  ValueDistribution.uniformInterval_hasDerivAt_cdf a b hab price hprice

end UniformInterval

/-! ## Uniform posted pricing -/

section UniformPricing

variable (a b continuationValue acquisitionCost : ℝ) (hab : a < b)

/-- The uniform virtual-surplus weight uses the chosen constant density
representative and is valid at both support endpoints. -/
example (value : ℝ) (hvalue : value ∈ Icc a b) :
    (ValueDistribution.uniformInterval a b hab).virtualSurplusWeight
        (fun _ : ℝ ↦ 1 / (b - a)) value =
      (2 * value - b) / (b - a) :=
  ValueDistribution.uniformInterval_virtualSurplusWeight a b hab value hvalue

/-- The candidate price is explicitly the midpoint formula clamped to the
value interval. -/
example :
    ValueDistribution.uniformOptimalPrice a b continuationValue =
      max a (min b ((b + continuationValue) / 2)) :=
  rfl

example :
    ValueDistribution.uniformOptimalPrice a b continuationValue ∈ Icc a b :=
  ValueDistribution.uniformOptimalPrice_mem_Icc a b continuationValue hab

/-- The lower-endpoint formula needs only the peak inequality. -/
example (hpeak : (b + continuationValue) / 2 ≤ a) :
    ValueDistribution.uniformOptimalPrice a b continuationValue = a :=
  ValueDistribution.uniformOptimalPrice_eq_left a b continuationValue hpeak

/-- Above the support, the unconstrained peak is clamped to the upper endpoint. -/
example (hpeak : b ≤ (b + continuationValue) / 2) :
    ValueDistribution.uniformOptimalPrice a b continuationValue = b :=
  ValueDistribution.uniformOptimalPrice_eq_right a b continuationValue hab hpeak

/-- A feasible unconstrained peak is unchanged, including at either endpoint. -/
example (hpeak : (b + continuationValue) / 2 ∈ Icc a b) :
    ValueDistribution.uniformOptimalPrice a b continuationValue = (b + continuationValue) / 2 :=
  ValueDistribution.uniformOptimalPrice_eq_peak a b continuationValue hpeak

/-- The price formula uses the existing seller-profit objective. -/
example (price : ℝ) (hprice : price ∈ Icc a b) :
    (ValueDistribution.uniformInterval a b hab).sellerProfit
        (postedPriceProblem a b price) continuationValue acquisitionCost =
      continuationValue - acquisitionCost +
        (price - continuationValue) * ((b - price) / (b - a)) :=
  ValueDistribution.sellerProfit_uniformInterval a b hab
    price continuationValue acquisitionCost hprice

/-- The chosen price maximizes profit over the stated feasible interval. -/
example :
    IsMaxOn
      (fun price ↦
        (ValueDistribution.uniformInterval a b hab).sellerProfit
          (postedPriceProblem a b price) continuationValue acquisitionCost)
      (Icc a b) (ValueDistribution.uniformOptimalPrice a b continuationValue) :=
  ValueDistribution.isMaxOn_sellerProfit_uniformInterval a b hab
    continuationValue acquisitionCost

/-- Any feasible maximizing price is the chosen price, including in the
boundary regimes. -/
example (price : ℝ) (hprice : price ∈ Icc a b)
    (hmax : IsMaxOn
      (fun candidate ↦
        (ValueDistribution.uniformInterval a b hab).sellerProfit
          (postedPriceProblem a b candidate) continuationValue acquisitionCost)
      (Icc a b) price) :
    price = ValueDistribution.uniformOptimalPrice a b continuationValue :=
  ValueDistribution.uniformOptimalPrice_eq_of_isMaxOn_sellerProfit_uniformInterval
    a b hab price continuationValue acquisitionCost hprice hmax

/-- At an interior uniform optimum, virtual value equals continuation value. -/
example (hpeak : (b + continuationValue) / 2 ∈ Ioo a b) :
    (ValueDistribution.uniformInterval a b hab).virtualValue
        (fun _ : ℝ ↦ 1 / (b - a)) ((b + continuationValue) / 2) =
      continuationValue :=
  ValueDistribution.uniformInterval_virtualValue_eq_continuationValue_of_interior
    a b hab continuationValue hpeak

end UniformPricing

/-! ## Comparative statics of uniform posted prices -/

section UniformPricingComparativeStatics

variable (a b continuationValue : ℝ)

example : Monotone (fun lowerEndpoint ↦
    ValueDistribution.uniformOptimalPrice lowerEndpoint b continuationValue) :=
  ValueDistribution.monotone_uniformOptimalPrice_lowerEndpoint b continuationValue

example : Monotone (fun upperEndpoint ↦
    ValueDistribution.uniformOptimalPrice a upperEndpoint continuationValue) :=
  ValueDistribution.monotone_uniformOptimalPrice_upperEndpoint a continuationValue

example : Monotone (fun continuation ↦
    ValueDistribution.uniformOptimalPrice a b continuation) :=
  ValueDistribution.monotone_uniformOptimalPrice_continuationValue a b

example (a₁ a₂ : ℝ)
    (h₁ : (b + continuationValue) / 2 ∈ Ioo a₁ b)
    (h₂ : (b + continuationValue) / 2 ∈ Ioo a₂ b) :
    ValueDistribution.uniformOptimalPrice a₂ b continuationValue =
      ValueDistribution.uniformOptimalPrice a₁ b continuationValue :=
  ValueDistribution.uniformOptimalPrice_lowerEndpoint_eq_of_interior
    a₁ a₂ b continuationValue h₁ h₂

example (b₁ b₂ : ℝ)
    (h₁ : (b₁ + continuationValue) / 2 ∈ Ioo a b₁)
    (h₂ : (b₂ + continuationValue) / 2 ∈ Ioo a b₂) :
    ValueDistribution.uniformOptimalPrice a b₂ continuationValue -
        ValueDistribution.uniformOptimalPrice a b₁ continuationValue = (b₂ - b₁) / 2 :=
  ValueDistribution.uniformOptimalPrice_upperEndpoint_sub_of_interior
    a b₁ b₂ continuationValue h₁ h₂

example (r₁ r₂ : ℝ)
    (h₁ : (b + r₁) / 2 ∈ Ioo a b)
    (h₂ : (b + r₂) / 2 ∈ Ioo a b) :
    ValueDistribution.uniformOptimalPrice a b r₂ -
        ValueDistribution.uniformOptimalPrice a b r₁ = (r₂ - r₁) / 2 :=
  ValueDistribution.uniformOptimalPrice_continuationValue_sub_of_interior
    a b r₁ r₂ h₁ h₂

end UniformPricingComparativeStatics

/-! ## Economic boundaries -/

/-- In the no-sale regime, a price outside the support ties the selected endpoint.
The uniqueness theorem's feasible-price restriction therefore matters. -/
example (acquisitionCost : ℝ) :
    (ValueDistribution.uniformInterval 0 1 (by norm_num)).sellerProfit
        (postedPriceProblem 0 1 1) 2 acquisitionCost =
      (ValueDistribution.uniformInterval 0 1 (by norm_num)).sellerProfit
        (postedPriceProblem 0 1 2) 2 acquisitionCost := by
  let D := ValueDistribution.uniformInterval 0 1 (by norm_num)
  have noSale (price : ℝ) (hprice : 1 ≤ price) :
      D.sellerProfit (postedPriceProblem 0 1 price) 2 acquisitionCost =
        2 - acquisitionCost := by
    have hone : D.probAtLeast 1 = 0 := by
      rw [ValueDistribution.uniformInterval_probAtLeast 0 1 (by norm_num) 1 (by norm_num)]
      norm_num
    have hzero : D.probAtLeast price = 0 :=
      le_antisymm ((D.antitone_probAtLeast hprice).trans_eq hone) (D.probAtLeast_nonneg price)
    rw [ValueDistribution.sellerProfit_postedPriceProblem, hzero, mul_zero, add_zero]
  exact (noSale 1 (by norm_num)).trans (noSale 2 (by norm_num)).symm

/-- The interior virtual-value equation need not hold at a boundary optimum:
with continuation value -2 the selected price is 0, whose virtual value is -1. -/
example :
    (ValueDistribution.uniformInterval 0 1 (by norm_num)).virtualValue
      (fun _ : ℝ ↦ 1) 0 ≠ (-2 : ℝ) := by
  simp only [ValueDistribution.virtualValue, ValueDistribution.virtualSurplusWeight]
  rw [ValueDistribution.uniformInterval_probAtLeast 0 1 (by norm_num) 0 (by norm_num)]
  norm_num

/-- Posted-price allocation has a genuine expectation for every probability law,
including laws without a finite first moment. -/
example (D : ValueDistribution) (a b price : ℝ) :
    Integrable (fun value ↦ (postedPriceProblem a b price).q value) (D : Measure ℝ) := by
  simp_rw [postedPriceProblem_q]
  exact (integrable_const (1 : ℝ)).indicator measurableSet_Ici

end UniformPricingCompatibility

end
