module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!

# Envelope Theorem

This file contains the mathematical heart of the Envelope Theorem.
We introduced a structure `EnvelopSetUpMathsCore`, which captures the analytic hypotheses:
- a bounded interval `[a, b]`
- a marginal allocation `q : ℝ → ℝ` taking values in `[0, 1]`,
- an interim utility `U : ℝ → ℝ` satisfying the incentive-compatibility inequality:
  for all `s, s' ∈ [a, b]`, `(s - s') * q s' ≤ U s - U s'`

## Main results

- `EnvelopSetUpMathsCore.lipschitz`: `U` is 1-Lipschitz on `[a, b]`.
- `EnvelopSetUpMathsCore.aeDifferentiable`: for almost every `s ∈ [a, b]`, the deriviate of `U` is
  equal to `q`.
- `EnvelopSetUpMathsCore.integral_rep`: `U s = U a + ∫ ψ in a..s, q ψ`.

-/

@[expose] public section

section analysis

open MeasureTheory Filter Topology Asymptotics

/-- The mathematical setup for the Envelope Theorem. -/
structure EnvelopSetUpMathsCore where
  /-- lower bound -/
  a : ℝ
  /-- upper bound -/
  b : ℝ
  -- We don't even need `a < b`: if `b ≤ a`, the theorem is vacuously true.
  -- hab : a < b
  /-- marginal allocation -/
  q : ℝ → ℝ
  /-- allocations are probabilities: q takes values in [0, 1] on [a, b] -/
  q_range : ∀ s ∈ Set.Icc a b, q s ∈ Set.Icc 0 1
  /-- interim utility -/
  U : ℝ → ℝ
  /-- incentive compatibility in analytic form.-/
  ic : ∀ s ∈ Set.Icc a b, ∀ s' ∈ Set.Icc a b, (s - s') * q s' ≤ U s - U s'

namespace EnvelopSetUpMathsCore

variable (ℰ : EnvelopSetUpMathsCore)

lemma lipschitz : LipschitzOnWith 1 ℰ.U (Set.Icc ℰ.a ℰ.b) := fun x hx y hy => by
  simp only [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq]
  refine ENNReal.ofReal_le_ofReal <| abs_le.2 ⟨?_, ?_⟩

  all_goals have hic1 := ℰ.ic x hx y hy
  all_goals have hic2 : ℰ.U x - ℰ.U y ≤ (x - y) * ℰ.q x := by linarith [ℰ.ic y hy x hx]
  all_goals have hqx := ℰ.q_range x hx
  all_goals have hqy := ℰ.q_range y hy

  all_goals nlinarith [abs_nonneg (x - y), neg_abs_le (x - y), le_abs_self (x - y),
    mul_nonneg (show 0 ≤ (x - y) + |x - y| by linarith [neg_abs_le (x - y)]) hqy.1,
    mul_nonneg (show 0 ≤ |x - y| - (x - y) by linarith [le_abs_self (x - y)]) hqx.1,
    mul_nonneg (abs_nonneg (x - y)) <| show 0 ≤ 1 - ℰ.q y by linarith [hqy.2],
    mul_nonneg (abs_nonneg (x - y)) <| show 0 ≤ 1 - ℰ.q x by linarith [hqx.2]]

private lemma q_monotoneOn (ℰ : EnvelopSetUpMathsCore) : MonotoneOn ℰ.q (Set.Icc ℰ.a ℰ.b) :=
  fun x hx y hy hxy => by
    rcases hxy.lt_or_eq with hlt | rfl
    · by_contra! h
      have h1 := ℰ.ic x hx y hy
      have h2 := ℰ.ic y hy x hx
      nlinarith [mul_pos (show 0 < y - x by linarith) (show 0 < ℰ.q x - ℰ.q y by linarith)]
    · rfl

/-- The HasDerivAt argument at a continuity point of q in the interior of [a,b]. -/
private lemma hasDerivAt_of_continuousAt {ℰ : EnvelopSetUpMathsCore} {x : ℝ}
    (hx_a : ℰ.a < x) (hx_b : x < ℰ.b) (hq_cont : ContinuousAt ℰ.q x) :
    HasDerivAt ℰ.U (ℰ.q x) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc

  have hx_icc : x ∈ Set.Icc ℰ.a ℰ.b := ⟨le_of_lt hx_a, le_of_lt hx_b⟩
  have hmaps : Tendsto (x + ·) (𝓝 0) (𝓝 x) := by
    simpa using (show ContinuousAt (fun h : ℝ => x + h) 0 from
      continuousAt_const.add continuousAt_id).tendsto
  have hIcc : ∀ᶠ h in 𝓝 0, x + h ∈ Set.Icc ℰ.a ℰ.b := hmaps (Icc_mem_nhds hx_a hx_b)
  have hq_tend : Tendsto (fun h => ℰ.q (x + h) - ℰ.q x) (𝓝 0) (𝓝 0) := by
    simpa using (hq_cont.tendsto.comp hmaps).sub_const (ℰ.q x)
  have hq_small : ∀ᶠ h in 𝓝 0, ‖ℰ.q (x + h) - ℰ.q x‖ < c := by
    filter_upwards [hq_tend (Metric.ball_mem_nhds 0 hc)] with h hh
    rwa [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hh
  filter_upwards [hIcc, hq_small] with h hIcc_h hq_h

  have e_nonneg : 0 ≤ ℰ.U (x + h) - ℰ.U x - h * ℰ.q x := by
    linarith [ℰ.ic (x + h) hIcc_h x hx_icc, ℰ.ic x hx_icc (x + h) hIcc_h]
  simp only [Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg e_nonneg]

  calc ℰ.U (x + h) - ℰ.U x - h * ℰ.q x
    _ ≤ h * (ℰ.q (x + h) - ℰ.q x) := by
      linarith [ℰ.ic (x + h) hIcc_h x hx_icc, ℰ.ic x hx_icc (x + h) hIcc_h]
    _ ≤ |h * (ℰ.q (x + h) - ℰ.q x)| := le_abs_self _
    _ = |h| * |ℰ.q (x + h) - ℰ.q x| := abs_mul _ _
    _ ≤ |h| * c :=
      mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs] at hq_h; linarith) (abs_nonneg h)
    _ = c * |h| := mul_comm _ _

lemma aeDifferentiable : ∀ᵐ s ∂volume.restrict (Set.Icc ℰ.a ℰ.b), HasDerivAt ℰ.U (ℰ.q s) s := by
  open Set in
  rw [ae_restrict_iff' measurableSet_Icc]
  -- Countable bad set: discontinuity points of q (within [a,b]) ∪ endpoints
  have hbad : Set.Countable <|
      {x ∈ Set.Icc ℰ.a ℰ.b | ¬ContinuousWithinAt ℰ.q (Set.Icc ℰ.a ℰ.b) x} ∪ {ℰ.a, ℰ.b} :=
    ℰ.q_monotoneOn.countable_not_continuousWithinAt.union <| countable_insert.mpr <|
      countable_singleton _
  filter_upwards [hbad.ae_notMem volume] with s hs hsab
  simp only [mem_union, mem_sep_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
  push_neg at hs
  have has : ℰ.a < s := lt_of_le_of_ne hsab.1 <| Ne.symm hs.2.1
  have hsb : s < ℰ.b := lt_of_le_of_ne hsab.2 hs.2.2
  exact hasDerivAt_of_continuousAt has hsb <|  (hs.1 hsab).continuousAt <| Icc_mem_nhds has hsb

lemma integral_rep (s) (hs : s ∈ Set.Icc ℰ.a ℰ.b) : ℰ.U s = ℰ.U ℰ.a + ∫ ψ in ℰ.a..s, ℰ.q ψ := by
  open Set in
  have hU_deriv : ∀ t ∈ Set.Ioo (min ℰ.a s) (max ℰ.a s) \
      {x ∈ Set.Icc ℰ.a ℰ.b | ¬ContinuousWithinAt ℰ.q (Set.Icc ℰ.a ℰ.b) x},
      HasDerivAt ℰ.U (ℰ.q t) t := by
    rintro t ⟨ht_int, ht_bad⟩
    simp only [mem_sep_iff, not_and, not_not, min_eq_left hs.1, max_eq_right hs.1] at ht_bad ht_int
    have ht_a : ℰ.a < t := ht_int.1
    have ht_b : t < ℰ.b := lt_of_lt_of_le ht_int.2 hs.2
    exact hasDerivAt_of_continuousAt ht_a ht_b <|
      ht_bad ⟨le_of_lt ht_a, le_of_lt ht_b⟩ |>.continuousAt (Icc_mem_nhds ht_a ht_b)

  have := integral_eq_of_hasDerivAt_off_countable ℰ.U ℰ.q
    ℰ.q_monotoneOn.countable_not_continuousWithinAt
    (ℰ.lipschitz.continuousOn.mono <|
      by simpa [Set.uIcc_of_le hs.1] using Icc_subset_Icc_right hs.2)
    hU_deriv
    (ℰ.q_monotoneOn.mono <|
      by simpa [Set.uIcc_of_le hs.1] using Set.Icc_subset_Icc_right hs.2).intervalIntegrable
  grind

end EnvelopSetUpMathsCore

end analysis

end
