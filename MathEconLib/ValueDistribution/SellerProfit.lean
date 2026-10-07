module

public import MathEconLib.ValueDistribution.ExpectedPayment

/-!
# Seller Profit and Virtual Surplus

This file rewrites the existing single-buyer seller objective using the
distributional virtual-surplus identities. The seller's continuation value
and unconditional acquisition cost remain separate scalar arguments of the
existing `sellerProfit` definition.
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set

universe u

namespace ValueDistribution

/-! ## Expected allocation under a density -/

/-- Under absolute continuity and bounded support, expected allocation is the
induced allocation integrated against the canonical real-valued density. -/
theorem expectedAllocation_eq_intervalIntegral_q_mul_realDensity
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume) :
    D.expectedAllocation P =
      ∫ value in P.lowestType..P.highestType,
        P.q value * D.realDensity value := by
  rw [expectedAllocation,
    D.integral_eq_intervalIntegral_realDensity_mul
      P.q horder hsupport hD]
  apply intervalIntegral.integral_congr
  intro value _
  ring

/-! ## Seller profit from virtual surplus -/

/-- Expected seller profit is continuation value minus acquisition cost and
lowest-type utility, plus allocation-weighted virtual surplus net of the
seller's continuation value. -/
theorem sellerProfit_eq_virtualSurplus_realDensity
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (continuationValue acquisitionCost : ℝ)
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume) :
    D.sellerProfit P continuationValue acquisitionCost =
      continuationValue - acquisitionCost - P.U P.lowestType +
        ∫ value in P.lowestType..P.highestType,
          P.q value *
            (D.virtualSurplusWeight D.realDensity value -
              continuationValue * D.realDensity value) := by
  unfold sellerProfit
  rw [D.expectedPayment_eq_integral_q_mul_virtualSurplusWeight_realDensity
      P horder hsupport hD,
    D.expectedAllocation_eq_intervalIntegral_q_mul_realDensity
      P horder hsupport hD]
  have hvirtual :=
    D.intervalIntegrable_q_mul_virtualSurplusWeight_realDensity
      P horder hsupport hD
  have hallocation :=
    D.intervalIntegrable_q_mul_realDensity P horder hD
  have hcombine :
      (∫ value in P.lowestType..P.highestType,
          P.q value *
            D.virtualSurplusWeight D.realDensity value) -
        continuationValue *
          ∫ value in P.lowestType..P.highestType,
            P.q value * D.realDensity value =
        ∫ value in P.lowestType..P.highestType,
          P.q value *
            (D.virtualSurplusWeight D.realDensity value -
              continuationValue * D.realDensity value) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_sub hvirtual
      (hallocation.const_mul continuationValue)]
    apply intervalIntegral.integral_congr
    intro value _
    ring
  linear_combination hcombine

/-- Any density representative agreeing almost everywhere with the canonical
real density on the type interval gives the same seller-profit formula. -/
theorem sellerProfit_eq_virtualSurplus
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (density : ℝ → ℝ)
    (continuationValue acquisitionCost : ℝ)
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict P.typeInterval] D.realDensity) :
    D.sellerProfit P continuationValue acquisitionCost =
      continuationValue - acquisitionCost - P.U P.lowestType +
        ∫ value in P.lowestType..P.highestType,
          P.q value *
            (D.virtualSurplusWeight density value -
              continuationValue * density value) := by
  rw [D.sellerProfit_eq_virtualSurplus_realDensity P
    continuationValue acquisitionCost horder hsupport hD]
  have hdensityOnIntegral :
      density =ᵐ[volume.restrict
        (uIoc P.lowestType P.highestType)] D.realDensity := by
    apply ae_restrict_of_ae_restrict_of_subset uIoc_subset_uIcc
    simpa [uIcc_of_le horder] using hdensity
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [hdensityOnIntegral] with value hdensityValue
  simp [virtualSurplusWeight, hdensityValue]

/-- For an absolutely continuous value distribution, the chosen-density
seller-profit formula can be written using one minus the CDF. -/
theorem sellerProfit_eq_virtualSurplus_cdf
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (density : ℝ → ℝ)
    (continuationValue acquisitionCost : ℝ)
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict P.typeInterval] D.realDensity) :
    D.sellerProfit P continuationValue acquisitionCost =
      continuationValue - acquisitionCost - P.U P.lowestType +
        ∫ value in P.lowestType..P.highestType,
          P.q value *
            ((value * density value -
                (1 - cdf (D : Measure ℝ) value)) -
              continuationValue * density value) := by
  rw [D.sellerProfit_eq_virtualSurplus P density
    continuationValue acquisitionCost horder hsupport hD hdensity]
  letI : NoAtoms (D : Measure ℝ) :=
    ⟨fun _ => hD (by simp)⟩
  congr 1
  apply intervalIntegral.integral_congr
  intro value _
  change P.q value *
      (D.virtualSurplusWeight density value -
        continuationValue * density value) =
    P.q value *
      ((value * density value -
          (1 - cdf (D : Measure ℝ) value)) -
        continuationValue * density value)
  rw [D.virtualSurplusWeight_eq_sub_one_sub_cdf density value]

end ValueDistribution

end

end MathEconLib
