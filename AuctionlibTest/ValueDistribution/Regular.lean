/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

import Auctionlib.ValueDistribution.Regular

/-!
# Compatibility checks for regular value distributions

Compile-time pins for virtual-value continuity and expected-payment identities.
-/

open MeasureTheory Set SingleParameterProblem

noncomputable section

namespace ValueDistributionRegularCompatibility

universe u

variable (D : ValueDistribution) (density : ℝ → ℝ) (lower upper : ℝ)

/-! ## Virtual values and regularity -/

example :
    D.IsRegular density lower upper ↔
      MonotoneOn (D.virtualValue density) (Icc lower upper) :=
  Iff.rfl

example (hdensity : Measurable density) : Measurable (D.virtualSurplusWeight density) :=
  D.measurable_virtualSurplusWeight hdensity

example (hdensity : Measurable density) : Measurable (D.virtualValue density) :=
  D.measurable_virtualValue hdensity

example [NoAtoms (D : Measure ℝ)] (hcont : ContinuousOn density (Icc lower upper))
    (hpos : ∀ v ∈ Icc lower upper, 0 < density v) :
    ContinuousOn (D.virtualValue density) (Icc lower upper) :=
  D.continuousOn_virtualValue hcont hpos

example (hD : (D : Measure ℝ) ≪ volume)
    (hdensity : density =ᵐ[volume.restrict (Icc lower upper)] D.realDensity)
    (hpos : ∀ᵐ v ∂(volume.restrict (Icc lower upper)), 0 < density v) :
    volume.restrict (Icc lower upper) ≪ (D : Measure ℝ) :=
  D.absolutelyContinuous_volume_restrict_of_ae_pos hD hdensity hpos

example (g : ℝ → ℝ) (horder : lower ≤ upper)
    (hsupport : D.IsSupportedOnInterval lower upper)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity : density =ᵐ[volume.restrict (Icc lower upper)] D.realDensity)
    (hpos : ∀ᵐ v ∂(volume.restrict (Icc lower upper)), 0 < density v) :
    (∫ v, g v * D.virtualValue density v ∂(D : Measure ℝ)) =
      ∫ v in lower..upper, g v * D.virtualSurplusWeight density v :=
  D.integral_mul_virtualValue_eq_intervalIntegral_mul_virtualSurplusWeight
    g density horder hsupport hD hdensity hpos

/-! ## Expected payments -/

section Payment

variable {Action : Type u} (P : SingleParameterProblem Action) [HasEnvelopeIC P]
  (horder : P.lowestType ≤ P.highestType)
  (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
  (hD : (D : Measure ℝ) ≪ volume)
  (hdensity : density =ᵐ[volume.restrict P.typeInterval] D.realDensity)
  (hpos : ∀ᵐ v ∂(volume.restrict P.typeInterval), 0 < density v)

example :
    D.expectedPayment P =
      (∫ v, P.q v * D.virtualValue density v ∂(D : Measure ℝ)) -
        P.U P.lowestType :=
  D.expectedPayment_eq_integral_q_mul_virtualValue
    P density horder hsupport hD hdensity hpos

example (hU0 : P.HasZeroLowestTypeUtility) :
    D.expectedPayment P = ∫ v, P.q v * D.virtualValue density v ∂(D : Measure ℝ) :=
  D.expectedPayment_eq_integral_q_mul_virtualValue_of_hasZeroLowestTypeUtility
    P density horder hsupport hD hdensity hpos hU0

example (hIR : P.IsIndividuallyRational) :
    D.expectedPayment P ≤ ∫ v, P.q v * D.virtualValue density v ∂(D : Measure ℝ) :=
  D.expectedPayment_le_integral_q_mul_virtualValue
    P density horder hsupport hD hdensity hpos hIR

end Payment

end ValueDistributionRegularCompatibility

end
