/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

import Auctionlib.ValueDistribution.Ironing

/-!
# Compatibility checks for ironing

Compile-time pins for generic score ironing and its single-parameter corollaries.
-/

open MeasureTheory Set SingleParameterProblem

noncomputable section

namespace ValueDistributionIroningCompatibility

universe u

variable (D : ValueDistribution) (ψ : ℝ → ℝ) (lower upper : ℝ)
  (hsupport : D.IsSupportedOnInterval lower upper)
  (hψ : ContinuousOn ψ (Icc lower upper))

example : Monotone (D.ironed ψ) :=
  D.monotone_ironed ψ hsupport hψ

example : Measurable (D.ironed ψ) :=
  D.measurable_ironed ψ hsupport hψ

example [NoAtoms (D : Measure ℝ)] {x : ℝ → ℝ}
    (hx : ∀ v ∈ Icc lower upper, x v ∈ Icc (0 : ℝ) 1)
    (hmono : MonotoneOn x (Icc lower upper)) :
    (∫ v, x v * ψ v ∂(D : Measure ℝ)) ≤
      ∫ v, x v * D.ironed ψ v ∂(D : Measure ℝ) :=
  D.integral_mul_le_integral_mul_ironed ψ hsupport hψ hx hmono

section NoOp

variable [NoAtoms (D : Measure ℝ)]
  (hvol : volume.restrict (Icc lower upper) ≪ (D : Measure ℝ))
  (hmono : MonotoneOn ψ (Icc lower upper))

example {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    D.ironedQuantileScore ψ t = D.quantileScore ψ t :=
  D.ironedQuantileScore_eq_quantileScore_of_monotoneOn
    ψ hsupport hvol hψ hmono ht

example {v : ℝ} (hv : v ∈ Ioo lower upper) :
    D.ironed ψ v = ψ v :=
  D.ironed_eq_of_monotoneOn ψ hsupport hvol hψ hmono hv

end NoOp

section ReducedProblem

variable {Action : Type u} (P : SingleParameterProblem Action) [HasEnvelopeIC P]
  [NoAtoms (D : Measure ℝ)]
  (hsupportP : D.IsSupportedOnInterval P.lowestType P.highestType)
  (hψP : ContinuousOn ψ P.typeInterval)

example :
    (∫ v, P.reduce.q v * ψ v ∂(D : Measure ℝ)) ≤
      ∫ v, P.reduce.q v * D.ironed ψ v ∂(D : Measure ℝ) :=
  D.integral_q_mul_le_integral_q_mul_ironed P.reduce ψ hsupportP hψP

example
    (hflat : ∀ v ∈ P.reduce.typeInterval, ∀ w ∈ P.reduce.typeInterval,
      D.ironed ψ v = D.ironed ψ w → P.reduce.q v = P.reduce.q w) :
    (∫ v, P.reduce.q v * ψ v ∂(D : Measure ℝ)) =
      ∫ v, P.reduce.q v * D.ironed ψ v ∂(D : Measure ℝ) :=
  D.integral_q_mul_eq_integral_q_mul_ironed P.reduce ψ hsupportP hψP hflat

end ReducedProblem

section VirtualValue

variable {Action : Type u} (P : SingleParameterProblem Action) [HasEnvelopeIC P]
  (density : ℝ → ℝ) (horder : P.lowestType ≤ P.highestType)
  (hsupportP : D.IsSupportedOnInterval P.lowestType P.highestType)
  (hD : (D : Measure ℝ) ≪ volume)
  (hdensity : density =ᵐ[volume.restrict P.typeInterval] D.realDensity)
  (hcont : ContinuousOn density P.typeInterval)
  (hpos : ∀ v ∈ P.typeInterval, 0 < density v)

example (hIR : P.IsIndividuallyRational) :
    D.expectedPayment P ≤
      ∫ v, P.q v * D.ironed (D.virtualValue density) v ∂(D : Measure ℝ) :=
  D.expectedPayment_le_integral_q_mul_ironed_virtualValue
    P density horder hsupportP hD hdensity hcont hpos hIR

example (hreg : D.IsRegular density P.lowestType P.highestType)
    {v : ℝ} (hv : v ∈ Ioo P.lowestType P.highestType) :
    D.ironed (D.virtualValue density) v = D.virtualValue density v :=
  D.ironed_virtualValue_eq_of_isRegular density hsupportP hD hdensity
    hcont hpos hreg hv

end VirtualValue

end ValueDistributionIroningCompatibility

end
