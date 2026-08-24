/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.ForMathlib.AbsolutelyContinuous
public import Auctionlib.ForMathlib.CDF
public import Auctionlib.ValueDistribution.ExpectedPayment

/-!
# Regular value distributions and virtual-value revenue identities

Regularity is monotonicity of the virtual value on the support interval. This file also converts
the existing virtual-surplus-weight revenue identity into the familiar virtual-value form when a
chosen density is positive almost everywhere.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set SingleParameterProblem

noncomputable section

namespace ValueDistribution

/-- A value distribution is regular for a chosen density on `[lower, upper]` when its virtual value
is monotone there. -/
def IsRegular (D : ValueDistribution) (density : ℝ → ℝ) (lower upper : ℝ) : Prop :=
  MonotoneOn (D.virtualValue density) (Icc lower upper)

/-- Virtual-surplus weight is measurable when the chosen density is measurable. -/
theorem measurable_virtualSurplusWeight (D : ValueDistribution) {density : ℝ → ℝ}
    (hdensity : Measurable density) : Measurable (D.virtualSurplusWeight density) :=
  (measurable_id.mul hdensity).sub D.antitone_probAtLeast.measurable

/-- Virtual value is measurable when the chosen density is measurable. -/
theorem measurable_virtualValue (D : ValueDistribution) {density : ℝ → ℝ}
    (hdensity : Measurable density) : Measurable (D.virtualValue density) :=
  (D.measurable_virtualSurplusWeight hdensity).div hdensity

/-- For an atomless distribution and a continuous positive density, virtual value is continuous on
the support interval. -/
theorem continuousOn_virtualValue (D : ValueDistribution) [NoAtoms (D : Measure ℝ)]
    {density : ℝ → ℝ} {lower upper : ℝ} (hcont : ContinuousOn density (Icc lower upper))
    (hpos : ∀ v ∈ Icc lower upper, 0 < density v) :
    ContinuousOn (D.virtualValue density) (Icc lower upper) := by
  have hnum : ContinuousOn
      (fun v => v * density v - (1 - cdf (D : Measure ℝ) v)) (Icc lower upper) :=
    (continuousOn_id.mul hcont).sub
      (continuousOn_const.sub ProbabilityTheory.continuous_cdf.continuousOn)
  have hquot := hnum.div hcont fun v hv => ne_of_gt (hpos v hv)
  refine hquot.congr fun v _ => ?_
  rw [Pi.div_apply, virtualValue, D.virtualSurplusWeight_eq_sub_one_sub_cdf]

/-- Positivity of a chosen density representative gives reverse absolute continuity of Lebesgue
measure on the support interval with respect to the value distribution. -/
theorem absolutelyContinuous_volume_restrict_of_ae_pos (D : ValueDistribution)
    {density : ℝ → ℝ} {lower upper : ℝ} (hD : (D : Measure ℝ) ≪ volume)
    (hdensity : density =ᵐ[volume.restrict (Icc lower upper)] D.realDensity)
    (hpos : ∀ᵐ v ∂(volume.restrict (Icc lower upper)), 0 < density v) :
    volume.restrict (Icc lower upper) ≪ (D : Measure ℝ) := by
  apply Measure.restrict_absolutelyContinuous_of_ae_rnDeriv_pos hD measurableSet_Icc
  have hlt : ∀ᵐ v ∂(volume.restrict (Icc lower upper)),
      (D : Measure ℝ).rnDeriv volume v < ⊤ :=
    ae_restrict_of_ae ((D : Measure ℝ).rnDeriv_lt_top volume)
  filter_upwards [hdensity, hpos, hlt] with v hdensity_v hpos_v hlt_v
  change density v = ((D : Measure ℝ).rnDeriv volume v).toReal at hdensity_v
  rw [hdensity_v] at hpos_v
  exact (ENNReal.toReal_pos_iff.mp hpos_v).1

/-- Multiplying virtual value by a positive density recovers virtual-surplus weight under the
integral. -/
theorem integral_mul_virtualValue_eq_intervalIntegral_mul_virtualSurplusWeight
    (D : ValueDistribution) (g density : ℝ → ℝ) {lower upper : ℝ}
    (horder : lower ≤ upper) (hsupport : D.IsSupportedOnInterval lower upper)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity : density =ᵐ[volume.restrict (Icc lower upper)] D.realDensity)
    (hpos : ∀ᵐ v ∂(volume.restrict (Icc lower upper)), 0 < density v) :
    (∫ v, g v * D.virtualValue density v ∂(D : Measure ℝ)) =
      ∫ v in lower..upper, g v * D.virtualSurplusWeight density v := by
  rw [D.integral_eq_intervalIntegral_realDensity_mul
    (fun v => g v * D.virtualValue density v) horder hsupport hD]
  have hdensity' : density =ᵐ[volume.restrict (uIoc lower upper)] D.realDensity := by
    apply ae_restrict_of_ae_restrict_of_subset uIoc_subset_uIcc
    simpa [uIcc_of_le horder] using hdensity
  have hpos' : ∀ᵐ v ∂(volume.restrict (uIoc lower upper)), 0 < density v := by
    apply ae_restrict_of_ae_restrict_of_subset uIoc_subset_uIcc
    simpa [uIcc_of_le horder] using hpos
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [hdensity', hpos'] with v hdensity_v hpos_v
  rw [← hdensity_v,
    D.virtualSurplusWeight_eq_density_mul_virtualValue density v (ne_of_gt hpos_v)]
  ring

/-- Expected payment equals expected virtual value minus the lowest type's utility. -/
theorem expectedPayment_eq_integral_q_mul_virtualValue
    {Action : Type*} (D : ValueDistribution) (P : SingleParameterProblem Action)
    [HasEnvelopeIC P] (density : ℝ → ℝ) (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity : density =ᵐ[volume.restrict P.typeInterval] D.realDensity)
    (hpos : ∀ᵐ v ∂(volume.restrict P.typeInterval), 0 < density v) :
    D.expectedPayment P =
      (∫ v, P.q v * D.virtualValue density v ∂(D : Measure ℝ)) -
        P.U P.lowestType := by
  rw [D.expectedPayment_eq_integral_q_mul_virtualSurplusWeight
    P density horder hsupport hD hdensity]
  rw [D.integral_mul_virtualValue_eq_intervalIntegral_mul_virtualSurplusWeight
    P.q density horder hsupport hD hdensity hpos]

/-- With zero utility for the lowest type, expected payment equals expected virtual value. -/
theorem expectedPayment_eq_integral_q_mul_virtualValue_of_hasZeroLowestTypeUtility
    {Action : Type*} (D : ValueDistribution) (P : SingleParameterProblem Action)
    [HasEnvelopeIC P] (density : ℝ → ℝ) (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity : density =ᵐ[volume.restrict P.typeInterval] D.realDensity)
    (hpos : ∀ᵐ v ∂(volume.restrict P.typeInterval), 0 < density v)
    (hU0 : P.HasZeroLowestTypeUtility) :
    D.expectedPayment P = ∫ v, P.q v * D.virtualValue density v ∂(D : Measure ℝ) := by
  rw [D.expectedPayment_eq_integral_q_mul_virtualValue
    P density horder hsupport hD hdensity hpos, hU0, sub_zero]

/-- Individual rationality bounds expected payment by expected virtual value. -/
theorem expectedPayment_le_integral_q_mul_virtualValue
    {Action : Type*} (D : ValueDistribution) (P : SingleParameterProblem Action)
    [HasEnvelopeIC P] (density : ℝ → ℝ) (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity : density =ᵐ[volume.restrict P.typeInterval] D.realDensity)
    (hpos : ∀ᵐ v ∂(volume.restrict P.typeInterval), 0 < density v)
    (hIR : P.IsIndividuallyRational) :
    D.expectedPayment P ≤ ∫ v, P.q v * D.virtualValue density v ∂(D : Measure ℝ) := by
  rw [D.expectedPayment_eq_integral_q_mul_virtualValue
    P density horder hsupport hD hdensity hpos]
  exact sub_le_self _ (hIR P.lowestType ⟨le_rfl, horder⟩)

end ValueDistribution

end
