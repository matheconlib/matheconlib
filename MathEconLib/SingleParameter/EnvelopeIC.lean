module

public import MathEconLib.SingleParameter.IC
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# The Envelope Theorem for Single-Parameter Problems

This file develops the analytic consequences of envelope incentive
compatibility for an arbitrary `SingleParameterProblem`.

The central conclusions are:

* `SingleParameterProblem.lipschitz`: equilibrium utility is Lipschitz;
* `SingleParameterProblem.q_monotoneOn`: the induced allocation is monotone;
* `SingleParameterProblem.aeDifferentiable`: the derivative of utility equals
  the induced allocation almost everywhere;
* `SingleParameterProblem.integral_rep`: utility is its value at the lowest
  type plus the integral of the induced allocation.

The action type remains arbitrary throughout. Thus these results apply to
bids, reports, contract choices, and other screening problems whose utility is
affine in the one-dimensional type. They do not cover genuinely nonseparable
type-action utility.
-/

namespace MathEconLib

@[expose] public section

open Set MeasureTheory Filter Topology Asymptotics

universe u

namespace SingleParameterProblem

variable {Action : Type u} (P : SingleParameterProblem Action)

/-! ## Envelope consequences -/

/-- Equilibrium utility is `1`-Lipschitz on the type interval. -/
theorem lipschitz [HasEnvelopeIC P] :
    LipschitzOnWith 1 P.U P.typeInterval := fun x hx y hy => by
  simp only [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq]
  have hic_lower := HasEnvelopeIC.envelopeIC x hx y hy
  have hic_upper : P.U x - P.U y ≤ (x - y) * P.q x := by
    linarith [HasEnvelopeIC.envelopeIC y hy x hx]
  have hq_x := P.q_range x
  have hq_y := P.q_range y
  refine ENNReal.ofReal_le_ofReal <| abs_le.2 ⟨?_, ?_⟩ <;>
  nlinarith [abs_nonneg (x - y), neg_abs_le (x - y), le_abs_self (x - y),
    mul_nonneg (show 0 ≤ (x - y) + |x - y| by linarith [neg_abs_le (x - y)]) hq_y.1,
    mul_nonneg (show 0 ≤ |x - y| - (x - y) by linarith [le_abs_self (x - y)]) hq_x.1,
    mul_nonneg (abs_nonneg (x - y)) <| show 0 ≤ 1 - P.q y by linarith [hq_y.2],
    mul_nonneg (abs_nonneg (x - y)) <| show 0 ≤ 1 - P.q x by linarith [hq_x.2]]

/-- The induced allocation is monotone on the type interval. -/
theorem q_monotoneOn [HasEnvelopeIC P] :
    MonotoneOn P.q P.typeInterval := fun x hx y hy hxy => by
  rcases hxy.lt_or_eq with hlt | rfl
  · by_contra! h
    have h1 := HasEnvelopeIC.envelopeIC x hx y hy
    have h2 := HasEnvelopeIC.envelopeIC y hy x hx
    nlinarith [mul_pos (show 0 < y - x by linarith) (show 0 < P.q x - P.q y by linarith)]
  · rfl

/-- At an interior point where `q` is continuous, the derivative of `U`
equals `q`. -/
private theorem hasDerivAt_of_continuousAt
    {Action : Type u} {P : SingleParameterProblem Action} [HasEnvelopeIC P] {x : ℝ}
    (hx_lo : P.lowestType < x) (hx_hi : x < P.highestType)
    (hq_cont : ContinuousAt P.q x) :
    HasDerivAt P.U (P.q x) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  have hx_icc : x ∈ P.typeInterval := ⟨le_of_lt hx_lo, le_of_lt hx_hi⟩
  have hmaps : Tendsto (x + ·) (𝓝 0) (𝓝 x) := by
    simpa using (show ContinuousAt (fun h : ℝ => x + h) 0 from
      continuousAt_const.add continuousAt_id).tendsto
  have h_in_interval : ∀ᶠ h in 𝓝 0, x + h ∈ P.typeInterval :=
    hmaps (Icc_mem_nhds hx_lo hx_hi)
  have hq_tend : Tendsto (fun h => P.q (x + h) - P.q x) (𝓝 0) (𝓝 0) := by
    simpa using (hq_cont.tendsto.comp hmaps).sub_const (P.q x)
  have hq_small : ∀ᶠ h in 𝓝 0, ‖P.q (x + h) - P.q x‖ < c := by
    filter_upwards [hq_tend (Metric.ball_mem_nhds 0 hc)] with h hh
    rwa [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hh
  filter_upwards [h_in_interval, hq_small] with h hxh hq_h
  have e_nonneg : 0 ≤ P.U (x + h) - P.U x - h * P.q x := by
    linarith [HasEnvelopeIC.envelopeIC (x + h) hxh x hx_icc,
      HasEnvelopeIC.envelopeIC x hx_icc (x + h) hxh]
  simp only [Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg e_nonneg]
  calc
    P.U (x + h) - P.U x - h * P.q x
        ≤ h * (P.q (x + h) - P.q x) := by
          linarith [HasEnvelopeIC.envelopeIC (x + h) hxh x hx_icc,
            HasEnvelopeIC.envelopeIC x hx_icc (x + h) hxh]
    _ ≤ |h * (P.q (x + h) - P.q x)| := le_abs_self _
    _ = |h| * |P.q (x + h) - P.q x| := abs_mul _ _
    _ ≤ |h| * c :=
      mul_le_mul_of_nonneg_left
        (by rw [Real.norm_eq_abs] at hq_h; linarith) (abs_nonneg h)
    _ = c * |h| := mul_comm _ _

/-- Equilibrium utility has derivative `q` almost everywhere on the type
interval. -/
theorem aeDifferentiable [HasEnvelopeIC P] :
    ∀ᵐ v ∂volume.restrict P.typeInterval, HasDerivAt P.U (P.q v) v := by
  rw [ae_restrict_iff' measurableSet_Icc]
  -- A monotone function has only countably many discontinuities. Adding the
  -- two endpoints still leaves a measure-zero exceptional set.
  have h_exceptional : Set.Countable <|
      {x ∈ P.typeInterval | ¬ContinuousWithinAt P.q P.typeInterval x} ∪
        {P.lowestType, P.highestType} :=
    P.q_monotoneOn.countable_not_continuousWithinAt.union <| countable_insert.mpr <|
      countable_singleton _
  filter_upwards [h_exceptional.ae_notMem volume] with v hv hv_interval
  simp only [mem_union, mem_sep_iff, mem_insert_iff, mem_singleton_iff, not_or] at hv
  push_neg at hv
  have hv_low : P.lowestType < v :=
    lt_of_le_of_ne hv_interval.1 <| Ne.symm hv.2.1
  have hv_high : v < P.highestType :=
    lt_of_le_of_ne hv_interval.2 hv.2.2
  exact hasDerivAt_of_continuousAt hv_low hv_high <|
    (hv.1 hv_interval).continuousAt <| Icc_mem_nhds hv_low hv_high

/-- **Integral representation of utility.**

For every type `v` in the type interval,

`U(v) = U(lowestType) + ∫ lowestType..v, q(w) dw`.
-/
theorem integral_rep [HasEnvelopeIC P]
    (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.U v = P.U P.lowestType + ∫ w in P.lowestType..v, P.q w := by
  have hU_deriv : ∀ t ∈ Ioo (min P.lowestType v) (max P.lowestType v) \
      {x ∈ P.typeInterval | ¬ContinuousWithinAt P.q P.typeInterval x},
      HasDerivAt P.U (P.q t) t := by
    rintro t ⟨ht_interval, ht_continuous⟩
    simp only [mem_sep_iff, not_and, not_not] at ht_continuous
    simp only [min_eq_left hv.1, max_eq_right hv.1] at ht_interval
    have ht_low : P.lowestType < t := ht_interval.1
    have ht_high : t < P.highestType := lt_of_lt_of_le ht_interval.2 hv.2
    exact hasDerivAt_of_continuousAt ht_low ht_high <|
      (ht_continuous ⟨le_of_lt ht_low, le_of_lt ht_high⟩).continuousAt <|
        Icc_mem_nhds ht_low ht_high
  -- Apply the fundamental theorem of calculus away from the countable set
  -- where the monotone allocation can fail to be continuous.
  have hintegral := integral_eq_of_hasDerivAt_off_countable P.U P.q
    P.q_monotoneOn.countable_not_continuousWithinAt
    (P.lipschitz.continuousOn.mono <|
      by simpa [uIcc_of_le hv.1] using Icc_subset_Icc_right hv.2)
    hU_deriv
    (P.q_monotoneOn.mono <|
      by simpa [uIcc_of_le hv.1] using Icc_subset_Icc_right hv.2).intervalIntegrable
  -- `hintegral` writes the same equality with the integral on the left.
  grind

/-! ## Utility nonnegativity -/

/-- If the lowest type has nonnegative utility, then every type in the type
interval has nonnegative utility. -/
theorem U_nonneg [HasEnvelopeIC P]
    (hU0 : 0 ≤ P.U P.lowestType) (v : ℝ) (hv : v ∈ P.typeInterval) :
    0 ≤ P.U v := by
  rw [P.integral_rep v hv]
  exact add_nonneg hU0 <| intervalIntegral.integral_nonneg hv.1
    fun w _ => (P.q_range w).1

end SingleParameterProblem

end

end MathEconLib
