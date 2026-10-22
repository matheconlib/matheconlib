/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.SingleParameter.Payment
public import MathEconLib.ValueDistribution.Density
public import MathEconLib.ValueDistribution.SingleParameter
public import MathEconLib.ValueDistribution.TailIntegral
public import MathEconLib.ValueDistribution.VirtualValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Expected Payment and Virtual Surplus

This file combines the single-parameter payment identity with the
distributional tail-integral identity. The density-free theorem is primary;
virtual-surplus formulas follow under absolute continuity.

The proof uses a private clamped extension of the induced allocation. Under
envelope incentive compatibility, the allocation is monotone on the problem's
type interval. Clamping its argument to that interval produces a globally
monotone, hence measurable, function without imposing any restriction on the
problem's behavior at off-support types.
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set

universe u

namespace ValueDistribution

/-- Extend the induced allocation by holding it constant outside the type
interval. This is private analytic infrastructure for distributional proofs. -/
private noncomputable def clampedAllocation
    {Action : Type u} (P : SingleParameterProblem Action)
    (horder : P.lowestType ≤ P.highestType) (value : ℝ) : ℝ :=
  P.q (Set.projIcc P.lowestType P.highestType horder value)

/-- Clamping leaves an allocation unchanged at types inside the interval. -/
private theorem clampedAllocation_eq_of_mem
    {Action : Type u} (P : SingleParameterProblem Action)
    (horder : P.lowestType ≤ P.highestType)
    {value : ℝ} (hvalue : value ∈ P.typeInterval) :
    clampedAllocation P horder value = P.q value := by
  simp [clampedAllocation, Set.projIcc_of_mem horder hvalue]

/-- Envelope IC makes the clamped allocation globally monotone. -/
private theorem monotone_clampedAllocation
    {Action : Type u} (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType) :
    Monotone (clampedAllocation P horder) := by
  intro lowerValue upperValue hvalues
  unfold clampedAllocation
  exact P.q_monotoneOn
    (Set.projIcc P.lowestType P.highestType horder lowerValue).property
    (Set.projIcc P.lowestType P.highestType horder upperValue).property
    (Set.monotone_projIcc horder hvalues)

/-- The clamped allocation retains the allocation range `[0, 1]`. -/
private theorem clampedAllocation_range
    {Action : Type u} (P : SingleParameterProblem Action)
    (horder : P.lowestType ≤ P.highestType) (value : ℝ) :
    clampedAllocation P horder value ∈ Icc 0 1 :=
  P.q_range (Set.projIcc P.lowestType P.highestType horder value)

/-- The clamped allocation is measurable. -/
private theorem measurable_clampedAllocation
    {Action : Type u} (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType) :
    Measurable (clampedAllocation P horder) :=
  (monotone_clampedAllocation P horder).measurable

/-- The clamped allocation is integrable under any value distribution. -/
private theorem integrable_clampedAllocation
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType) :
    Integrable (clampedAllocation P horder) (D : Measure ℝ) := by
  apply Integrable.of_bound
    (measurable_clampedAllocation P horder).aestronglyMeasurable 1
  filter_upwards with value
  rw [Real.norm_eq_abs,
    abs_of_nonneg (clampedAllocation_range P horder value).1]
  exact (clampedAllocation_range P horder value).2

/-- Envelope IC supplies interval integrability of the induced allocation. -/
private theorem intervalIntegrable_q
    {Action : Type u} (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType) :
    IntervalIntegrable P.q volume P.lowestType P.highestType := by
  have hmonotone :
      MonotoneOn P.q (uIcc P.lowestType P.highestType) := by
    simpa [uIcc_of_le horder] using P.q_monotoneOn
  exact hmonotone.intervalIntegrable

/-- The value-weighted clamped allocation is integrable under bounded
support. -/
private theorem integrable_value_mul_clampedAllocation
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType) :
    Integrable
      (fun value => value * clampedAllocation P horder value)
      (D : Measure ℝ) := by
  apply Integrable.of_bound
    (measurable_id.mul (measurable_clampedAllocation P horder)).aestronglyMeasurable
    (max |P.lowestType| |P.highestType|)
  filter_upwards [hsupport] with value hvalue
  simp only [id_eq]
  have hq := clampedAllocation_range P horder value
  calc
    ‖value * clampedAllocation P horder value‖ =
        |value| * clampedAllocation P horder value := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hq.1]
    _ ≤ |value| * 1 :=
      mul_le_mul_of_nonneg_left hq.2 (abs_nonneg value)
    _ = |value| := mul_one _
    _ ≤ max |P.lowestType| |P.highestType| :=
      abs_le_max_abs_abs hvalue.1 hvalue.2

/-- The cumulative clamped allocation is integrable under bounded support. -/
private theorem integrable_intervalIntegral_clampedAllocation
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType) :
    Integrable
      (fun value =>
        ∫ cutoff in P.lowestType..value,
          clampedAllocation P horder cutoff)
      (D : Measure ℝ) := by
  have hcontinuous :
      Continuous fun value =>
        ∫ cutoff in P.lowestType..value,
          clampedAllocation P horder cutoff :=
    intervalIntegral.continuous_primitive
      (fun _ _ => (monotone_clampedAllocation P horder).intervalIntegrable)
      P.lowestType
  apply Integrable.of_bound hcontinuous.measurable.aestronglyMeasurable
    (P.highestType - P.lowestType)
  filter_upwards [hsupport] with value hvalue
  have hnorm :
      ‖∫ cutoff in P.lowestType..value,
          clampedAllocation P horder cutoff‖ ≤
        1 * |value - P.lowestType| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun cutoff _ => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (clampedAllocation_range P horder cutoff).1]
      exact (clampedAllocation_range P horder cutoff).2
  calc
    ‖∫ cutoff in P.lowestType..value,
        clampedAllocation P horder cutoff‖ ≤
        1 * |value - P.lowestType| := hnorm
    _ = value - P.lowestType := by
      rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hvalue.1)]
    _ ≤ P.highestType - P.lowestType :=
      sub_le_sub_right hvalue.2 P.lowestType

/-- On a supported interval endpoint, integrating the clamped allocation is
the same as integrating the original induced allocation. -/
private theorem intervalIntegral_clampedAllocation_eq
    {Action : Type u} (P : SingleParameterProblem Action)
    (horder : P.lowestType ≤ P.highestType)
    {value : ℝ} (hvalue : value ∈ P.typeInterval) :
    (∫ cutoff in P.lowestType..value,
        clampedAllocation P horder cutoff) =
      ∫ cutoff in P.lowestType..value, P.q cutoff := by
  apply intervalIntegral.integral_congr
  intro cutoff hcutoff
  apply clampedAllocation_eq_of_mem
  rw [uIcc_of_le hvalue.1] at hcutoff
  exact ⟨hcutoff.1, hcutoff.2.trans hvalue.2⟩

/-! ## Density-free expected payment -/

/-- **Density-free expected-payment identity.** Under envelope IC, expected
payment equals expected value-weighted allocation, minus lowest-type utility,
minus the allocation weighted by closed upper-tail probability.

No density or atomlessness assumption is required. -/
theorem expectedPayment_eq_integral_value_mul_q_sub_integral_tail
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType) :
    D.expectedPayment P =
      (∫ value, value * P.q value ∂(D : Measure ℝ)) -
        P.U P.lowestType -
        ∫ cutoff in P.lowestType..P.highestType,
          P.q cutoff * D.probAtLeast cutoff := by
  have hpayment_ae :
      (fun value => P.payment (P.strategy value)) =ᵐ[(D : Measure ℝ)]
        fun value =>
          value * clampedAllocation P horder value -
            P.U P.lowestType -
            ∫ cutoff in P.lowestType..value,
              clampedAllocation P horder cutoff := by
    filter_upwards [hsupport] with value hvalue
    rw [P.payment_identity value hvalue,
      clampedAllocation_eq_of_mem P horder hvalue,
      intervalIntegral_clampedAllocation_eq P horder hvalue]
  have hvalueAllocation_integrable :=
    integrable_value_mul_clampedAllocation D P horder hsupport
  have hcumulative_integrable :=
    integrable_intervalIntegral_clampedAllocation D P horder hsupport
  have hconstant_integrable :
      Integrable (fun _ : ℝ => P.U P.lowestType) (D : Measure ℝ) :=
    integrable_const _
  have hvalueAllocation :
      (∫ value,
          value * clampedAllocation P horder value ∂(D : Measure ℝ)) =
        ∫ value, value * P.q value ∂(D : Measure ℝ) := by
    apply integral_congr_ae
    filter_upwards [hsupport] with value hvalue
    rw [clampedAllocation_eq_of_mem P horder hvalue]
  have htail :
      (∫ value,
          (∫ cutoff in P.lowestType..value,
            clampedAllocation P horder cutoff) ∂(D : Measure ℝ)) =
        ∫ cutoff in P.lowestType..P.highestType,
          clampedAllocation P horder cutoff *
            D.probAtLeast cutoff := by
    apply D.integral_intervalIntegral_eq_integral_mul_probAtLeast
      horder hsupport (measurable_clampedAllocation P horder)
      (monotone_clampedAllocation P horder).intervalIntegrable
    intro cutoff _
    exact (clampedAllocation_range P horder cutoff).1
  have htailAllocation :
      (∫ cutoff in P.lowestType..P.highestType,
          clampedAllocation P horder cutoff * D.probAtLeast cutoff) =
        ∫ cutoff in P.lowestType..P.highestType,
          P.q cutoff * D.probAtLeast cutoff := by
    apply intervalIntegral.integral_congr
    intro cutoff hcutoff
    rw [uIcc_of_le horder] at hcutoff
    change clampedAllocation P horder cutoff * D.probAtLeast cutoff =
      P.q cutoff * D.probAtLeast cutoff
    rw [clampedAllocation_eq_of_mem P horder hcutoff]
  rw [expectedPayment, integral_congr_ae hpayment_ae]
  change
    (∫ value,
      (((fun value => value * clampedAllocation P horder value) -
        (fun _ : ℝ => P.U P.lowestType)) -
        (fun value =>
          ∫ cutoff in P.lowestType..value,
            clampedAllocation P horder cutoff)) value ∂(D : Measure ℝ)) = _
  have houterSub :
      (∫ value,
          (((fun value => value * clampedAllocation P horder value) -
            (fun _ : ℝ => P.U P.lowestType)) -
            (fun value =>
              ∫ cutoff in P.lowestType..value,
                clampedAllocation P horder cutoff)) value ∂(D : Measure ℝ)) =
        (∫ value,
            ((fun value => value * clampedAllocation P horder value) -
              (fun _ : ℝ => P.U P.lowestType)) value ∂(D : Measure ℝ)) -
          ∫ value,
            (∫ cutoff in P.lowestType..value,
              clampedAllocation P horder cutoff) ∂(D : Measure ℝ) := by
    simpa using
      integral_sub
        (hvalueAllocation_integrable.sub hconstant_integrable)
        hcumulative_integrable
  have hinnerSub :
      (∫ value,
          ((fun value => value * clampedAllocation P horder value) -
            (fun _ : ℝ => P.U P.lowestType)) value ∂(D : Measure ℝ)) =
        (∫ value,
          value * clampedAllocation P horder value ∂(D : Measure ℝ)) -
          ∫ _ : ℝ, P.U P.lowestType ∂(D : Measure ℝ) := by
    simpa using
      integral_sub hvalueAllocation_integrable hconstant_integrable
  have hconstant :
      (∫ _ : ℝ, P.U P.lowestType ∂(D : Measure ℝ)) =
        P.U P.lowestType := by
    simp
  rw [houterSub, hinnerSub, hconstant, hvalueAllocation, htail,
    htailAllocation]

/-! ## Density-based virtual surplus -/

/-- Absolute continuity removes the lower endpoint from an almost-sure closed
support interval. -/
private theorem ae_mem_Ioc_of_supported_of_absolutelyContinuous
    (D : ValueDistribution) {lower upper : ℝ}
    (hsupport : D.IsSupportedOnInterval lower upper)
    (hD : (D : Measure ℝ) ≪ volume) :
    ∀ᵐ value ∂(D : Measure ℝ), value ∈ Ioc lower upper := by
  have hlower : (D : Measure ℝ) {lower} = 0 :=
    hD (by simp)
  have hnotLower : ∀ᵐ value ∂(D : Measure ℝ), value ∉ ({lower} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hlower
  filter_upwards [hsupport, hnotLower] with value hvalue hne
  have hne' : value ≠ lower := by
    simpa using hne
  exact ⟨lt_of_le_of_ne hvalue.1 hne'.symm, hvalue.2⟩

/-- Under absolute continuity and bounded support, expected value-weighted
allocation is an interval integral against the canonical real density. -/
private theorem integral_value_mul_q_eq_intervalIntegral_realDensity
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume) :
    (∫ value, value * P.q value ∂(D : Measure ℝ)) =
      ∫ value in P.lowestType..P.highestType,
        P.q value * (value * D.realDensity value) := by
  have hIoc :=
    ae_mem_Ioc_of_supported_of_absolutelyContinuous D hsupport hD
  have hindicator :
      (∫ value, value * P.q value ∂(D : Measure ℝ)) =
        ∫ value,
          (Ioc P.lowestType P.highestType).indicator
            (fun value => value * P.q value) value ∂(D : Measure ℝ) := by
    apply integral_congr_ae
    filter_upwards [hIoc] with value hvalue
    rw [indicator_of_mem hvalue]
  have hdensity := D.integral_eq_integral_realDensity_mul
    ((Ioc P.lowestType P.highestType).indicator
      (fun value => value * P.q value)) hD
  have hvolume :
      (∫ value,
          D.realDensity value *
            (Ioc P.lowestType P.highestType).indicator
              (fun value => value * P.q value) value ∂volume) =
        ∫ value in Ioc P.lowestType P.highestType,
          D.realDensity value * (value * P.q value) ∂volume := by
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with value
    by_cases hvalue : value ∈ Ioc P.lowestType P.highestType <;>
      simp [hvalue]
  rw [hindicator, hdensity, hvolume,
    ← intervalIntegral.integral_of_le horder]
  apply intervalIntegral.integral_congr
  intro value _
  ring

/-- The canonical density contribution to virtual surplus is interval
integrable under envelope IC and bounded support. -/
private theorem intervalIntegrable_q_mul_value_mul_realDensity
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume) :
    IntervalIntegrable
      (fun value => P.q value * (value * D.realDensity value))
      volume P.lowestType P.highestType := by
  have hglobal :
      Integrable
        (fun value =>
          D.realDensity value *
            (value * clampedAllocation P horder value)) volume := by
    simpa [realDensity] using
      (integrable_rnDeriv_smul_iff hD).mpr
        (integrable_value_mul_clampedAllocation D P horder hsupport)
  apply IntervalIntegrable.congr _ hglobal.intervalIntegrable
  intro value hvalue
  rw [uIoc_of_le horder] at hvalue
  have hvalueClosed : value ∈ P.typeInterval :=
    ⟨hvalue.1.le, hvalue.2⟩
  change D.realDensity value *
      (value * clampedAllocation P horder value) =
    P.q value * (value * D.realDensity value)
  rw [clampedAllocation_eq_of_mem P horder hvalueClosed]
  ring

/-- Allocation times closed-tail demand is interval integrable under envelope
IC. -/
private theorem intervalIntegrable_q_mul_probAtLeast
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType) :
    IntervalIntegrable
      (fun value => P.q value * D.probAtLeast value)
      volume P.lowestType P.highestType := by
  have hclampedIntegrableOn :
      IntegrableOn
        (fun value =>
          clampedAllocation P horder value * D.probAtLeast value)
        (Ioc P.lowestType P.highestType) volume := by
    apply Integrable.of_bound
      ((measurable_clampedAllocation P horder).mul
        D.antitone_probAtLeast.measurable).aestronglyMeasurable.restrict
      1
    filter_upwards with value
    have hq := clampedAllocation_range P horder value
    have hprobNonneg := D.probAtLeast_nonneg value
    have hprobOne := D.probAtLeast_le_one value
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hq.1 hprobNonneg)]
    exact mul_le_one₀ hq.2 hprobNonneg hprobOne
  have hclampedIntervalIntegrable :
      IntervalIntegrable
        (fun value =>
          clampedAllocation P horder value * D.probAtLeast value)
        volume P.lowestType P.highestType :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le horder).mpr
      hclampedIntegrableOn
  apply IntervalIntegrable.congr _ hclampedIntervalIntegrable
  intro value hvalue
  rw [uIoc_of_le horder] at hvalue
  change clampedAllocation P horder value * D.probAtLeast value =
    P.q value * D.probAtLeast value
  rw [clampedAllocation_eq_of_mem P horder
    ⟨hvalue.1.le, hvalue.2⟩]

/-- Under envelope IC and absolute continuity, allocation times the canonical
real density is interval integrable. -/
theorem intervalIntegrable_q_mul_realDensity
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType)
    (hD : (D : Measure ℝ) ≪ volume) :
    IntervalIntegrable
      (fun value => P.q value * D.realDensity value)
      volume P.lowestType P.highestType := by
  have hglobal :
      Integrable
        (fun value =>
          D.realDensity value * clampedAllocation P horder value)
        volume := by
    simpa [realDensity] using
      (integrable_rnDeriv_smul_iff hD).mpr
        (integrable_clampedAllocation D P horder)
  apply IntervalIntegrable.congr _ hglobal.intervalIntegrable
  intro value hvalue
  rw [uIoc_of_le horder] at hvalue
  change D.realDensity value * clampedAllocation P horder value =
    P.q value * D.realDensity value
  rw [clampedAllocation_eq_of_mem P horder
    ⟨hvalue.1.le, hvalue.2⟩]
  ring

/-- Under envelope IC, absolute continuity, and bounded support, allocation
times the canonical virtual-surplus weight is interval integrable. -/
theorem intervalIntegrable_q_mul_virtualSurplusWeight_realDensity
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume) :
    IntervalIntegrable
      (fun value =>
        P.q value * D.virtualSurplusWeight D.realDensity value)
      volume P.lowestType P.highestType := by
  have hdensity :=
    intervalIntegrable_q_mul_value_mul_realDensity
      D P horder hsupport hD
  have htail := intervalIntegrable_q_mul_probAtLeast D P horder
  apply IntervalIntegrable.congr _ (hdensity.sub htail)
  intro value _
  simp only [virtualSurplusWeight]
  ring

/-- **Canonical virtual-surplus expected-payment identity.** For an
absolutely continuous value distribution, expected payment is induced
allocation integrated against the canonical virtual-surplus weight, minus
lowest-type utility. -/
theorem expectedPayment_eq_integral_q_mul_virtualSurplusWeight_realDensity
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume) :
    D.expectedPayment P =
      (∫ value in P.lowestType..P.highestType,
        P.q value *
          D.virtualSurplusWeight D.realDensity value) -
        P.U P.lowestType := by
  have hdensity :=
    intervalIntegrable_q_mul_value_mul_realDensity
      D P horder hsupport hD
  have htail := intervalIntegrable_q_mul_probAtLeast D P horder
  rw [D.expectedPayment_eq_integral_value_mul_q_sub_integral_tail
      P horder hsupport,
    integral_value_mul_q_eq_intervalIntegral_realDensity
      D P horder hsupport hD]
  have hcombine :
      (∫ value in P.lowestType..P.highestType,
          P.q value * (value * D.realDensity value)) -
        ∫ value in P.lowestType..P.highestType,
          P.q value * D.probAtLeast value =
        ∫ value in P.lowestType..P.highestType,
          P.q value *
            D.virtualSurplusWeight D.realDensity value := by
    rw [← intervalIntegral.integral_sub hdensity htail]
    apply intervalIntegral.integral_congr
    intro value _
    simp only [virtualSurplusWeight]
    ring
  calc
    (∫ value in P.lowestType..P.highestType,
        P.q value * (value * D.realDensity value)) -
          P.U P.lowestType -
        ∫ value in P.lowestType..P.highestType,
          P.q value * D.probAtLeast value =
      ((∫ value in P.lowestType..P.highestType,
          P.q value * (value * D.realDensity value)) -
        ∫ value in P.lowestType..P.highestType,
          P.q value * D.probAtLeast value) -
        P.U P.lowestType := by ring
    _ = (∫ value in P.lowestType..P.highestType,
          P.q value *
            D.virtualSurplusWeight D.realDensity value) -
        P.U P.lowestType := by rw [hcombine]

/-- **Chosen-density virtual-surplus expected-payment identity.** Any density
that agrees almost everywhere with the canonical real density on the type
interval gives the same virtual-surplus formula. -/
theorem expectedPayment_eq_integral_q_mul_virtualSurplusWeight
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (density : ℝ → ℝ)
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict P.typeInterval] D.realDensity) :
    D.expectedPayment P =
      (∫ value in P.lowestType..P.highestType,
        P.q value * D.virtualSurplusWeight density value) -
        P.U P.lowestType := by
  rw [D.expectedPayment_eq_integral_q_mul_virtualSurplusWeight_realDensity
    P horder hsupport hD]
  have hdensityOnIntegral :
      density =ᵐ[volume.restrict
        (uIoc P.lowestType P.highestType)] D.realDensity := by
    apply ae_restrict_of_ae_restrict_of_subset uIoc_subset_uIcc
    simpa [uIcc_of_le horder] using hdensity
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [hdensityOnIntegral] with value hdensityValue
  simp [virtualSurplusWeight, hdensityValue]

/-- **Atomless CDF expected-payment identity.** For an absolutely continuous
value distribution, closed-tail demand equals one minus the CDF, so the
chosen-density virtual-surplus formula has its familiar CDF form. -/
theorem expectedPayment_eq_integral_q_mul_sub_one_sub_cdf
    {Action : Type u} (D : ValueDistribution)
    (P : SingleParameterProblem Action)
    [SingleParameterProblem.HasEnvelopeIC P]
    (density : ℝ → ℝ)
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict P.typeInterval] D.realDensity) :
    D.expectedPayment P =
      (∫ value in P.lowestType..P.highestType,
        P.q value *
          (value * density value -
            (1 - cdf (D : Measure ℝ) value))) -
        P.U P.lowestType := by
  rw [D.expectedPayment_eq_integral_q_mul_virtualSurplusWeight
    P density horder hsupport hD hdensity]
  letI : NoAtoms (D : Measure ℝ) :=
    ⟨fun _ => hD (by simp)⟩
  congr 1
  apply intervalIntegral.integral_congr
  intro value _
  change P.q value * D.virtualSurplusWeight density value =
    P.q value *
      (value * density value - (1 - cdf (D : Measure ℝ) value))
  rw [D.virtualSurplusWeight_eq_sub_one_sub_cdf density value]

end ValueDistribution

end

end MathEconLib
