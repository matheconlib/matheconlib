module

public import Auctionlib.ValueDistribution.Demand
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Tail-Integral Identity for Value Distributions

This file develops the measure-theoretic identity that exchanges an integral
of cumulative quantities with an integral against upper-tail probability.

For ordered bounds `lower ≤ upper`, a distribution `D` supported on
`[lower, upper]`, and a nonnegative interval-integrable function `q`, the
principal theorem states

`∫ value, (∫ cutoff in lower..value, q cutoff) ∂D`

`= ∫ cutoff in lower..upper, q cutoff * D.probAtLeast cutoff`.

The theorem is density-free and uses the closed upper tail, so it remains
valid for continuous, discrete, and mixed distributions. Its proof first
encodes the triangular integration region as a nonnegative `ℝ≥0∞`-valued
kernel, applies Tonelli's theorem, and then converts back to ordinary real
integrals.

The analytic theorem requests measurability and interval integrability
directly. Later single-parameter results derive these facts from incentive
compatibility and the allocation range rather than expose redundant analytic
assumptions to economic users.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ValueDistribution

/-- The nonnegative kernel for the triangular region
`lower < cutoff ≤ upper` and `cutoff ≤ value`.

This is a private proof device. The public theorem is stated using ordinary
interval integrals and `probAtLeast`. -/
private noncomputable def tailKernel
    (lower upper : ℝ) (q : ℝ → ℝ) (value cutoff : ℝ) : ℝ≥0∞ :=
  if lower < cutoff ∧ cutoff ≤ upper ∧ cutoff ≤ value then
    ENNReal.ofReal (q cutoff)
  else 0

/-- The triangular kernel is measurable on the product of the value and
cutoff spaces whenever the underlying function is measurable. -/
private theorem measurable_tailKernel
    {lower upper : ℝ} {q : ℝ → ℝ}
    (hq : Measurable q) :
    Measurable (Function.uncurry (tailKernel lower upper q)) := by
  exact Measurable.ite
    ((measurableSet_lt measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_const).inter
        (measurableSet_le measurable_snd measurable_fst)))
    (ENNReal.measurable_ofReal.comp (hq.comp measurable_snd))
    measurable_const

/-- Interval integrability bounds the nonnegative integral that appears after
converting an ordinary real integral to an `ℝ≥0∞` integral. -/
private theorem setLIntegral_ofReal_lt_top
    {lower upper : ℝ} {q : ℝ → ℝ}
    (hq : IntervalIntegrable q volume lower upper) :
    (∫⁻ cutoff in Ioc lower upper,
      ENNReal.ofReal (q cutoff) ∂volume) < ∞ :=
  hq.1.setLIntegral_lt_top

/-- At a supported value, a cutoff slice of the triangular kernel is the
indicator of the interval from the lower endpoint to that value. -/
private theorem tailKernel_eq_indicator
    {lower upper value : ℝ} {q : ℝ → ℝ}
    (hvalue : value ∈ Icc lower upper) :
    (fun cutoff => tailKernel lower upper q value cutoff) =
      (Ioc lower value).indicator
        (fun cutoff => ENNReal.ofReal (q cutoff)) := by
  funext cutoff
  by_cases hlower : lower < cutoff
  · by_cases hcutoff : cutoff ≤ value
    · have hupper : cutoff ≤ upper := hcutoff.trans hvalue.2
      simp [tailKernel, hlower, hupper, hcutoff]
    · simp [tailKernel, hlower, hcutoff]
  · simp [tailKernel, hlower]

/-- For a value in the support interval, its cumulative ordinary integral is
the real value of the corresponding nonnegative kernel integral. -/
private theorem intervalIntegral_eq_toReal_lintegral_tailKernel
    {lower upper value : ℝ} {q : ℝ → ℝ}
    (hvalue : value ∈ Icc lower upper)
    (hq : Measurable q)
    (hq_nonneg : ∀ cutoff ∈ Ioc lower upper, 0 ≤ q cutoff) :
    (∫ cutoff in lower..value, q cutoff) =
      ENNReal.toReal
        (∫⁻ cutoff, tailKernel lower upper q value cutoff ∂volume) := by
  have hnonneg :
      0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioc lower value)] q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with cutoff hcutoff
    exact hq_nonneg cutoff ⟨hcutoff.1, hcutoff.2.trans hvalue.2⟩
  have hreal :
      (∫ cutoff in Ioc lower value, q cutoff ∂volume) =
        ENNReal.toReal
          (∫⁻ cutoff in Ioc lower value,
            ENNReal.ofReal (q cutoff) ∂volume) :=
    integral_eq_lintegral_of_nonneg_ae hnonneg
      hq.aestronglyMeasurable.restrict
  have hkernelIntegral :
      (∫⁻ cutoff, tailKernel lower upper q value cutoff ∂volume) =
        ∫⁻ cutoff in Ioc lower value,
          ENNReal.ofReal (q cutoff) ∂volume := by
    rw [tailKernel_eq_indicator hvalue,
      lintegral_indicator measurableSet_Ioc]
  calc
    (∫ cutoff in lower..value, q cutoff) =
        ∫ cutoff in Ioc lower value, q cutoff ∂volume :=
      intervalIntegral.integral_of_le hvalue.1
    _ = ENNReal.toReal
          (∫⁻ cutoff in Ioc lower value,
            ENNReal.ofReal (q cutoff) ∂volume) := hreal
    _ = ENNReal.toReal
          (∫⁻ cutoff, tailKernel lower upper q value cutoff ∂volume) :=
      congrArg ENNReal.toReal hkernelIntegral.symm

/-- Every supported-value slice has finite mass because it is bounded by the
nonnegative integral over the full interval. -/
private theorem lintegral_tailKernel_lt_top
    {lower upper value : ℝ} {q : ℝ → ℝ}
    (hvalue : value ∈ Icc lower upper)
    (hq : IntervalIntegrable q volume lower upper) :
    (∫⁻ cutoff, tailKernel lower upper q value cutoff ∂volume) < ∞ := by
  rw [tailKernel_eq_indicator hvalue,
    lintegral_indicator measurableSet_Ioc]
  exact lt_of_le_of_lt
    (lintegral_mono_set (Ioc_subset_Ioc_right hvalue.2))
    (setLIntegral_ofReal_lt_top hq)

/-- On the support interval, converting the cumulative real integral to
`ℝ≥0∞` recovers the corresponding kernel integral exactly. -/
private theorem ofReal_intervalIntegral_eq_lintegral_tailKernel
    {lower upper value : ℝ} {q : ℝ → ℝ}
    (hvalue : value ∈ Icc lower upper)
    (hq_measurable : Measurable q)
    (hq_integrable : IntervalIntegrable q volume lower upper)
    (hq_nonneg : ∀ cutoff ∈ Ioc lower upper, 0 ≤ q cutoff) :
    ENNReal.ofReal (∫ cutoff in lower..value, q cutoff) =
      ∫⁻ cutoff, tailKernel lower upper q value cutoff ∂volume := by
  rw [intervalIntegral_eq_toReal_lintegral_tailKernel hvalue
    hq_measurable hq_nonneg]
  exact ENNReal.ofReal_toReal
    (lintegral_tailKernel_lt_top hvalue hq_integrable).ne

/-- Tonelli's theorem exchanges value and cutoff integration for the
nonnegative triangular kernel. -/
private theorem lintegral_tailKernel_swap
    {D : ValueDistribution} {lower upper : ℝ} {q : ℝ → ℝ}
    (hq : Measurable q) :
    (∫⁻ value, ∫⁻ cutoff, tailKernel lower upper q value cutoff ∂volume ∂D) =
      ∫⁻ cutoff, ∫⁻ value, tailKernel lower upper q value cutoff ∂D ∂volume := by
  exact lintegral_lintegral_swap (measurable_tailKernel hq).aemeasurable

/-- Integrating a cutoff slice over values produces its constant weight
times the measure of the closed upper tail. -/
private theorem lintegral_tailKernel_value
    {D : ValueDistribution} {lower upper cutoff : ℝ} {q : ℝ → ℝ} :
    (∫⁻ value, tailKernel lower upper q value cutoff ∂D) =
      (Ioc lower upper).indicator
        (fun cutoff => ENNReal.ofReal (q cutoff) *
          (D : Measure ℝ) (Ici cutoff)) cutoff := by
  by_cases hcutoff : cutoff ∈ Ioc lower upper
  · have hslice :
        (fun value => tailKernel lower upper q value cutoff) =
          (Ici cutoff).indicator
            (fun _ => ENNReal.ofReal (q cutoff)) := by
      funext value
      by_cases hvalue : cutoff ≤ value <;>
        simp [tailKernel, hcutoff.1, hcutoff.2, hvalue]
    rw [hslice, lintegral_indicator_const measurableSet_Ici]
    simp [hcutoff]
  · have houtside : ¬(lower < cutoff ∧ cutoff ≤ upper) := by
      simpa [mem_Ioc] using hcutoff
    have hkernel :
        ∀ value, ¬(lower < cutoff ∧ cutoff ≤ upper ∧ cutoff ≤ value) :=
      fun _ h => houtside ⟨h.1, h.2.1⟩
    simp [tailKernel, hkernel, hcutoff]

/-- The real-valued demand API converts back to the underlying finite measure
of the closed upper tail. -/
private theorem ofReal_probAtLeast
    (D : ValueDistribution) (cutoff : ℝ) :
    ENNReal.ofReal (D.probAtLeast cutoff) =
      (D : Measure ℝ) (Ici cutoff) := by
  rw [probAtLeast, ProbabilityMeasure.coeFn_def]
  simp [ENNReal.coe_toNNReal
    (measure_ne_top (D : Measure ℝ) (Ici cutoff))]

/-- **Tail-integral identity.** The expected cumulative quantity below a
random value equals the interval integral of that quantity weighted by the
closed upper-tail probability.

This density-free form is valid for continuous, discrete, and mixed value
distributions. -/
theorem integral_intervalIntegral_eq_integral_mul_probAtLeast
    (D : ValueDistribution) {lower upper : ℝ}
    (horder : lower ≤ upper)
    (hsupport : D.IsSupportedOnInterval lower upper)
    {q : ℝ → ℝ}
    (hq_measurable : Measurable q)
    (hq_integrable : IntervalIntegrable q volume lower upper)
    (hq_nonneg : ∀ cutoff ∈ Icc lower upper, 0 ≤ q cutoff) :
    (∫ value, (∫ cutoff in lower..value, q cutoff) ∂D) =
      ∫ cutoff in lower..upper,
        q cutoff * D.probAtLeast cutoff := by
  have hcumulative_nonneg :
      0 ≤ᵐ[(D : Measure ℝ)]
        fun value => ∫ cutoff in lower..value, q cutoff := by
    filter_upwards [hsupport] with value hvalue
    exact intervalIntegral.integral_nonneg hvalue.1 fun cutoff hcutoff =>
      hq_nonneg cutoff ⟨hcutoff.1, hcutoff.2.trans hvalue.2⟩
  have hq_nonneg_Ioc :
      ∀ cutoff ∈ Ioc lower upper, 0 ≤ q cutoff :=
    fun cutoff hcutoff =>
      hq_nonneg cutoff ⟨hcutoff.1.le, hcutoff.2⟩
  have hcumulative_ae :
      (fun value => ∫ cutoff in lower..value, q cutoff) =ᵐ[(D : Measure ℝ)]
        fun value =>
          ENNReal.toReal
            (∫⁻ cutoff,
              tailKernel lower upper q value cutoff ∂volume) := by
    filter_upwards [hsupport] with value hvalue
    exact intervalIntegral_eq_toReal_lintegral_tailKernel hvalue
      hq_measurable hq_nonneg_Ioc
  have hcumulative_measurable :
      AEStronglyMeasurable
        (fun value => ∫ cutoff in lower..value, q cutoff)
        (D : Measure ℝ) := by
    have hkernel_integral_measurable :
        Measurable fun value =>
          ∫⁻ cutoff,
            tailKernel lower upper q value cutoff ∂volume :=
      (measurable_tailKernel hq_measurable).lintegral_prod_right
    exact hkernel_integral_measurable.ennreal_toReal.aestronglyMeasurable.congr
      hcumulative_ae.symm
  have hlhs_lintegral :
      (∫⁻ value,
          ENNReal.ofReal
            (∫ cutoff in lower..value, q cutoff) ∂D) =
        ∫⁻ value, ∫⁻ cutoff,
          tailKernel lower upper q value cutoff ∂volume ∂D := by
    apply lintegral_congr_ae
    filter_upwards [hsupport] with value hvalue
    exact ofReal_intervalIntegral_eq_lintegral_tailKernel hvalue
      hq_measurable hq_integrable hq_nonneg_Ioc
  have hrhs_nonneg :
      0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioc lower upper)]
        fun cutoff => q cutoff * D.probAtLeast cutoff := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with cutoff hcutoff
    exact mul_nonneg (hq_nonneg_Ioc cutoff hcutoff)
      (D.probAtLeast_nonneg cutoff)
  have hrhs_measurable :
      AEStronglyMeasurable
        (fun cutoff => q cutoff * D.probAtLeast cutoff)
        ((volume : Measure ℝ).restrict (Ioc lower upper)) := by
    have hproduct :
        Measurable fun cutoff => q cutoff * D.probAtLeast cutoff :=
      hq_measurable.mul D.antitone_probAtLeast.measurable
    exact hproduct.aestronglyMeasurable.restrict
  have hrhs_lintegral :
      (∫⁻ cutoff in Ioc lower upper,
          ENNReal.ofReal (q cutoff * D.probAtLeast cutoff) ∂volume) =
        ∫⁻ cutoff in Ioc lower upper,
          ENNReal.ofReal (q cutoff) *
            (D : Measure ℝ) (Ici cutoff) ∂volume := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro cutoff hcutoff
    change ENNReal.ofReal (q cutoff * D.probAtLeast cutoff) =
      ENNReal.ofReal (q cutoff) * (D : Measure ℝ) (Ici cutoff)
    rw [ENNReal.ofReal_mul (hq_nonneg_Ioc cutoff hcutoff),
      ofReal_probAtLeast]
  have hswapped :
      (∫⁻ cutoff, ∫⁻ value,
          tailKernel lower upper q value cutoff ∂D ∂volume) =
        ∫⁻ cutoff in Ioc lower upper,
          ENNReal.ofReal (q cutoff) *
            (D : Measure ℝ) (Ici cutoff) ∂volume := by
    simp_rw [lintegral_tailKernel_value]
    rw [lintegral_indicator measurableSet_Ioc]
  calc
    (∫ value, (∫ cutoff in lower..value, q cutoff) ∂D) =
        ENNReal.toReal
          (∫⁻ value,
            ENNReal.ofReal
              (∫ cutoff in lower..value, q cutoff) ∂D) :=
      integral_eq_lintegral_of_nonneg_ae hcumulative_nonneg
        hcumulative_measurable
    _ = ENNReal.toReal
          (∫⁻ value, ∫⁻ cutoff,
            tailKernel lower upper q value cutoff ∂volume ∂D) :=
      congrArg ENNReal.toReal hlhs_lintegral
    _ = ENNReal.toReal
          (∫⁻ cutoff, ∫⁻ value,
            tailKernel lower upper q value cutoff ∂D ∂volume) :=
      congrArg ENNReal.toReal
        (lintegral_tailKernel_swap hq_measurable)
    _ = ENNReal.toReal
          (∫⁻ cutoff in Ioc lower upper,
            ENNReal.ofReal (q cutoff) *
              (D : Measure ℝ) (Ici cutoff) ∂volume) :=
      congrArg ENNReal.toReal hswapped
    _ = ENNReal.toReal
          (∫⁻ cutoff in Ioc lower upper,
            ENNReal.ofReal
              (q cutoff * D.probAtLeast cutoff) ∂volume) :=
      congrArg ENNReal.toReal hrhs_lintegral.symm
    _ = ∫ cutoff in Ioc lower upper,
          q cutoff * D.probAtLeast cutoff ∂volume :=
      (integral_eq_lintegral_of_nonneg_ae hrhs_nonneg
        hrhs_measurable).symm
    _ = ∫ cutoff in lower..upper,
          q cutoff * D.probAtLeast cutoff :=
      (intervalIntegral.integral_of_le horder).symm

end ValueDistribution

end
