module

public import Auctionlib.ReducedForm.Basic

/-!
# Envelope IC (Level 0) — Envelope Theorem on `Mechanism`

`HasEnvelopeIC` is the weakest IC typeclass: the increasing-differences form.
It is sufficient for the full envelope theorem:

- `Mechanism.lipschitz`: `U` is 1-Lipschitz on the type interval.
- `ReducedForm.q_monotoneOn`: `q` is monotone on the type interval.
- `Mechanism.aeDifferentiable`: `U' = q` a.e. on the type interval.
- `Mechanism.integral_rep`: `U(s) = U(lowestType) + ∫ lowestType..s, q(ψ) dψ`.

All results are automatically available on any mechanism satisfying a stronger IC
(`HasTypeDeviationIC`, `HasUniversalIC`) via the instance chain.
-/

@[expose] public section

open Set MeasureTheory Filter Topology Asymptotics

namespace ReducedForm

variable (R : ReducedForm)

/-- **Envelope IC** (Level 0): the increasing-differences form of incentive
compatibility.  This is the weakest IC — sufficient for the envelope theorem. -/
class HasEnvelopeIC (R : ReducedForm) : Prop where
  envelopeIC : ∀ s ∈ R.typeInterval, ∀ s' ∈ R.typeInterval,
    (s - s') * R.q s' ≤ R.U s - R.U s'

/-! ### Envelope theorem -/

/-- `U` is 1-Lipschitz on the type interval. -/
theorem lipschitz [HasEnvelopeIC R] :
    LipschitzOnWith 1 R.U R.typeInterval := fun x hx y hy => by
  simp only [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq]
  have hic1 := HasEnvelopeIC.envelopeIC x hx y hy
  have hic2 : R.U x - R.U y ≤ (x - y) * R.q x := by
    linarith [HasEnvelopeIC.envelopeIC y hy x hx]
  have hqx := R.q_range x
  have hqy := R.q_range y
  refine ENNReal.ofReal_le_ofReal <| abs_le.2 ⟨?_, ?_⟩ <;>
  nlinarith [abs_nonneg (x - y), neg_abs_le (x - y), le_abs_self (x - y),
    mul_nonneg (show 0 ≤ (x - y) + |x - y| by linarith [neg_abs_le (x - y)]) hqy.1,
    mul_nonneg (show 0 ≤ |x - y| - (x - y) by linarith [le_abs_self (x - y)]) hqx.1,
    mul_nonneg (abs_nonneg (x - y)) <| show 0 ≤ 1 - R.q y by linarith [hqy.2],
    mul_nonneg (abs_nonneg (x - y)) <| show 0 ≤ 1 - R.q x by linarith [hqx.2]]

/-- `q` is monotone on the type interval. -/
theorem q_monotoneOn [HasEnvelopeIC R] :
    MonotoneOn R.q R.typeInterval := fun x hx y hy hxy => by
  rcases hxy.lt_or_eq with hlt | rfl
  · by_contra! h
    have h1 := HasEnvelopeIC.envelopeIC x hx y hy
    have h2 := HasEnvelopeIC.envelopeIC y hy x hx
    nlinarith [mul_pos (show 0 < y - x by linarith) (show 0 < R.q x - R.q y by linarith)]
  · rfl

/-- HasDerivAt at a continuity point of q in the interior of the type interval. -/
private theorem hasDerivAt_of_continuousAt {R : ReducedForm} [HasEnvelopeIC R] {x : ℝ}
    (hx_lo : R.lowestType < x) (hx_hi : x < R.highestType)
    (hq_cont : ContinuousAt R.q x) :
    HasDerivAt R.U (R.q x) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  have hx_icc : x ∈ R.typeInterval := ⟨le_of_lt hx_lo, le_of_lt hx_hi⟩
  have hmaps : Tendsto (x + ·) (𝓝 0) (𝓝 x) := by
    simpa using (show ContinuousAt (fun h : ℝ => x + h) 0 from
      continuousAt_const.add continuousAt_id).tendsto
  have hIcc : ∀ᶠ h in 𝓝 0, x + h ∈ R.typeInterval := hmaps (Icc_mem_nhds hx_lo hx_hi)
  have hq_tend : Tendsto (fun h => R.q (x + h) - R.q x) (𝓝 0) (𝓝 0) := by
    simpa using (hq_cont.tendsto.comp hmaps).sub_const (R.q x)
  have hq_small : ∀ᶠ h in 𝓝 0, ‖R.q (x + h) - R.q x‖ < c := by
    filter_upwards [hq_tend (Metric.ball_mem_nhds 0 hc)] with h hh
    rwa [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hh
  filter_upwards [hIcc, hq_small] with h hIcc_h hq_h
  have e_nonneg : 0 ≤ R.U (x + h) - R.U x - h * R.q x := by
    linarith [HasEnvelopeIC.envelopeIC (x + h) hIcc_h x hx_icc,
              HasEnvelopeIC.envelopeIC x hx_icc (x + h) hIcc_h]
  simp only [Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg e_nonneg]
  calc R.U (x + h) - R.U x - h * R.q x
    _ ≤ h * (R.q (x + h) - R.q x) := by
      linarith [HasEnvelopeIC.envelopeIC (x + h) hIcc_h x hx_icc,
                HasEnvelopeIC.envelopeIC x hx_icc (x + h) hIcc_h]
    _ ≤ |h * (R.q (x + h) - R.q x)| := le_abs_self _
    _ = |h| * |R.q (x + h) - R.q x| := abs_mul _ _
    _ ≤ |h| * c :=
      mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs] at hq_h; linarith) (abs_nonneg h)
    _ = c * |h| := mul_comm _ _

/-- `U` is differentiable a.e. on the type interval with derivative `q`. -/
theorem aeDifferentiable [HasEnvelopeIC R] :
    ∀ᵐ s ∂volume.restrict R.typeInterval, HasDerivAt R.U (R.q s) s := by
  rw [ae_restrict_iff' measurableSet_Icc]
  have hbad : Set.Countable <|
      {x ∈ R.typeInterval | ¬ContinuousWithinAt R.q R.typeInterval x} ∪
        {R.lowestType, R.highestType} :=
    R.q_monotoneOn.countable_not_continuousWithinAt.union <| countable_insert.mpr <|
      countable_singleton _
  filter_upwards [hbad.ae_notMem volume] with s hs hsab
  simp only [mem_union, mem_sep_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
  push_neg at hs
  have has : R.lowestType < s := lt_of_le_of_ne hsab.1 <| Ne.symm hs.2.1
  have hsb : s < R.highestType := lt_of_le_of_ne hsab.2 hs.2.2
  exact hasDerivAt_of_continuousAt has hsb <|
    (hs.1 hsab).continuousAt <| Icc_mem_nhds has hsb

/-- Integral representation: `U(s) = U(lowestType) + ∫ lowestType..s, q(ψ) dψ`. -/
theorem integral_rep [HasEnvelopeIC R]
    (s : ℝ) (hs : s ∈ R.typeInterval) :
    R.U s = R.U R.lowestType + ∫ ψ in R.lowestType..s, R.q ψ := by
  have hU_deriv : ∀ t ∈ Ioo (min R.lowestType s) (max R.lowestType s) \
      {x ∈ R.typeInterval | ¬ContinuousWithinAt R.q R.typeInterval x},
      HasDerivAt R.U (R.q t) t := by
    rintro t ⟨ht_int, ht_bad⟩
    simp only [mem_sep_iff, not_and, not_not, min_eq_left hs.1, max_eq_right hs.1] at ht_bad ht_int
    have ht_a : R.lowestType < t := ht_int.1
    have ht_b : t < R.highestType := lt_of_lt_of_le ht_int.2 hs.2
    exact hasDerivAt_of_continuousAt ht_a ht_b <|
      ht_bad ⟨le_of_lt ht_a, le_of_lt ht_b⟩ |>.continuousAt (Icc_mem_nhds ht_a ht_b)
  have := integral_eq_of_hasDerivAt_off_countable R.U R.q
    R.q_monotoneOn.countable_not_continuousWithinAt
    (R.lipschitz.continuousOn.mono <|
      by simpa [uIcc_of_le hs.1] using Icc_subset_Icc_right hs.2)
    hU_deriv
    (R.q_monotoneOn.mono <|
      by simpa [uIcc_of_le hs.1] using Icc_subset_Icc_right hs.2).intervalIntegrable
  grind

/-! ### Additional envelope consequences -/

/-- **Weak monotonicity.** If `winProb` is strictly monotone, then `strategy` is
weakly increasing on the type interval.

Proof: `q = winProb ∘ strategy` is nondecreasing by `q_monotoneOn`, and `winProb`
strictly increasing allows "inverting". -/
theorem strategy_monotoneOn [HasEnvelopeIC R]
    (hG : StrictMono R.winProb) :
    MonotoneOn R.strategy R.typeInterval :=
  fun _ hx _ hy hxy => hG.le_iff_le.mp (R.q_monotoneOn hx hy hxy)

/-- Non-negativity of equilibrium utility.  If `U(lowestType) ≥ 0` then
`U(v) ≥ 0` for all `v` in the type interval, since `q ≥ 0`. -/
theorem U_nonneg [HasEnvelopeIC R]
    (hU0 : 0 ≤ R.U R.lowestType) (v : ℝ) (hv : v ∈ R.typeInterval) :
    0 ≤ R.U v := by
  rw [R.integral_rep v hv]
  exact add_nonneg hU0 (intervalIntegral.integral_nonneg hv.1
    fun ψ hψ => (R.q_range ψ).1)

end ReducedForm

end
