module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!

# Envelope Theorem & Myerson's Lemma — Mathematical Core

This file contains the mathematical heart of the Envelope Theorem and Myerson's Lemma.

## Envelope Theorem

We introduced a structure `EnvelopeSetUpMathsCore`, which captures the analytic hypotheses:
- a bounded interval `[a, b]`
- a marginal allocation `q : ℝ → ℝ` taking values in `[0, 1]`,
- an interim utility `U : ℝ → ℝ` satisfying the incentive-compatibility inequality:
  for all `s, s' ∈ [a, b]`, `(s - s') * q s' ≤ U s - U s'`

### Main results

- `EnvelopeSetUpMathsCore.lipschitz`: `U` is 1-Lipschitz on `[a, b]`.
- `EnvelopeSetUpMathsCore.aeDifferentiable`: for almost every `s ∈ [a, b]`, the derivative of `U` is
  equal to `q`.
- `EnvelopeSetUpMathsCore.integral_rep`: `U s = U a + ∫ ψ in a..s, q ψ`.

## Myerson's Lemma

Two structures capture the two directions of the Myerson equivalence:

- `MyersonSetUpMathsCore`: the necessity direction.
  Extends `EnvelopeSetUpMathsCore` with a payment rule `t : ℝ → ℝ` and DSIC.
- `MyersonSufficiencySetup`: the sufficiency direction.
  Given a monotone allocation rule, the canonical integral payment formula yields DSIC.

### Main results

- `MyersonSetUpMathsCore.monotone_of_dsic`: DSIC ⟹ `q` monotone on `[a, b]`.
- `MyersonSetUpMathsCore.payment_identity`: DSIC ⟹ `t(s) = s · q(s) - U(a) - ∫_{a}^{s} q(ψ) dψ`.
- `MyersonSetUpMathsCore.payment_unique`: two DSIC payment rules with the same `q` and `U(a)` agree
  on `[a, b]`.
- `MyersonSufficiencySetup.dsic_of_monotone`: monotone `x` + integral payment ⟹ DSIC.

-/

@[expose] public section

section analysis

open MeasureTheory Filter Topology Asymptotics

/-- The mathematical setup for the Envelope Theorem. -/
structure EnvelopeSetUpMathsCore where
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

namespace EnvelopeSetUpMathsCore

variable (ℰ : EnvelopeSetUpMathsCore)

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

lemma q_monotoneOn (ℰ : EnvelopeSetUpMathsCore) : MonotoneOn ℰ.q (Set.Icc ℰ.a ℰ.b) :=
  fun x hx y hy hxy => by
    rcases hxy.lt_or_eq with hlt | rfl
    · by_contra! h
      have h1 := ℰ.ic x hx y hy
      have h2 := ℰ.ic y hy x hx
      nlinarith [mul_pos (show 0 < y - x by linarith) (show 0 < ℰ.q x - ℰ.q y by linarith)]
    · rfl

/-- The HasDerivAt argument at a continuity point of q in the interior of [a,b]. -/
private lemma hasDerivAt_of_continuousAt {ℰ : EnvelopeSetUpMathsCore} {x : ℝ}
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

end EnvelopeSetUpMathsCore

/-- The mathematical setup for Myerson's Lemma (necessity direction).
Extends `EnvelopeSetUpMathsCore` with a payment rule and DSIC condition. -/
structure MyersonSetUpMathsCore extends EnvelopeSetUpMathsCore where
  /-- payment rule -/
  t : ℝ → ℝ
  /-- Dominant-strategy incentive compatibility: for any types `s, s' ∈ [a, b]`,
      reporting truthfully (`s`) is weakly better than misreporting (`s'`). -/
  dsic : ∀ s ∈ Set.Icc a b, ∀ s' ∈ Set.Icc a b,
    s * q s' - t s' ≤ s * q s - t s
  /-- Coherence: the inherited utility equals `s * q s - t s` -/
  hU : ∀ s, U s = s * q s - t s

namespace MyersonSetUpMathsCore

/-- Smart constructor: builds a `MyersonSetUpMathsCore` from allocation `x`, payment `t`,
and DSIC, automatically deriving the incentive-compatibility inequality for the parent. -/
noncomputable def mk'
    (a b : ℝ) (x : ℝ → ℝ) (x_range : ∀ s ∈ Set.Icc a b, x s ∈ Set.Icc 0 1)
    (t : ℝ → ℝ)
    (dsic : ∀ s ∈ Set.Icc a b, ∀ s' ∈ Set.Icc a b,
      s * x s' - t s' ≤ s * x s - t s) :
    MyersonSetUpMathsCore where
  a := a
  b := b
  q := x
  q_range := x_range
  U := fun s => s * x s - t s
  ic := fun s hs s' hs' => by nlinarith [dsic s hs s' hs']
  t := t
  dsic := dsic
  hU := fun _ => rfl

variable (ℳ : MyersonSetUpMathsCore)

/-- Necessity: DSIC implies the allocation rule is monotone nondecreasing. -/
theorem monotone_of_dsic : MonotoneOn ℳ.q (Set.Icc ℳ.a ℳ.b) :=
  ℳ.toEnvelopeSetUpMathsCore.q_monotoneOn

/-- Payment identity: under DSIC, `t(s) = s · q(s) - U(a) - ∫_{a}^{s} q(ψ) dψ`. -/
theorem payment_identity (s : ℝ) (hs : s ∈ Set.Icc ℳ.a ℳ.b) :
    ℳ.t s = s * ℳ.q s - ℳ.U ℳ.a - ∫ ψ in ℳ.a..s, ℳ.q ψ := by
  have hrep := ℳ.toEnvelopeSetUpMathsCore.integral_rep s hs
  have hUs := ℳ.hU s
  linarith

/-- Payment uniqueness: under DSIC, the payment rule is uniquely determined by the allocation
    rule and the base utility `U(a)`. -/
theorem payment_unique (ℳ₂ : MyersonSetUpMathsCore)
    (h_a : ℳ.a = ℳ₂.a) (h_b : ℳ.b = ℳ₂.b)
    (h_q : ℳ.q = ℳ₂.q) (h_Ua : ℳ.U ℳ.a = ℳ₂.U ℳ₂.a)
    (s : ℝ) (hs : s ∈ Set.Icc ℳ.a ℳ.b) :
    ℳ.t s = ℳ₂.t s := by
  have h1 := ℳ.payment_identity s hs
  have h2 := ℳ₂.payment_identity s (show s ∈ Set.Icc ℳ₂.a ℳ₂.b by rwa [← h_a, ← h_b])
  rw [h_q, h_a] at h1
  rw [h_a] at h_Ua
  linarith

end MyersonSetUpMathsCore

/-- The mathematical setup for Myerson's Lemma (sufficiency direction). -/
structure MyersonSufficiencySetup where
  /-- lower bound -/
  a : ℝ
  /-- upper bound -/
  b : ℝ
  /-- allocation rule -/
  x : ℝ → ℝ
  /-- allocations are probabilities: x takes values in [0, 1] on [a, b] -/
  x_range : ∀ s ∈ Set.Icc a b, x s ∈ Set.Icc 0 1
  /-- monotone nondecreasing allocation -/
  x_mono : MonotoneOn x (Set.Icc a b)

namespace MyersonSufficiencySetup

variable (ℳ : MyersonSufficiencySetup)

/-- The canonical payment rule: `t(s) = s · x(s) - c - ∫_{a}^{s} x(ψ) dψ`. -/
noncomputable def t (c : ℝ) (s : ℝ) : ℝ :=
  s * ℳ.x s - c - ∫ ψ in ℳ.a..s, ℳ.x ψ

/-- Utility under the canonical payment rule: `U(s) = c + ∫_{a}^{s} x(ψ) dψ`. -/
noncomputable abbrev U (c : ℝ) (s : ℝ) : ℝ := c + ∫ ψ in ℳ.a..s, ℳ.x ψ

/-- Sufficiency: the canonical payment formula yields a DSIC mechanism. -/
theorem dsic_of_monotone (c : ℝ) :
    ∀ s ∈ Set.Icc ℳ.a ℳ.b, ∀ s' ∈ Set.Icc ℳ.a ℳ.b,
    s * ℳ.x s' - ℳ.t c s' ≤ s * ℳ.x s - ℳ.t c s := by
  intro s hs s' hs'
  simp only [t]
  have hab : ℳ.a ≤ ℳ.b := le_trans hs.1 hs.2
  have ha_mem : ℳ.a ∈ Set.Icc ℳ.a ℳ.b := ⟨le_refl _, hab⟩
  -- Integrability from monotonicity on the relevant sub-intervals
  have hint : IntervalIntegrable ℳ.x volume s' s :=
    (ℳ.x_mono.mono (Set.uIcc_subset_Icc hs' hs)).intervalIntegrable
  have hint' : IntervalIntegrable ℳ.x volume ℳ.a s' :=
    (ℳ.x_mono.mono (Set.uIcc_subset_Icc ha_mem hs')).intervalIntegrable
  -- Integral additivity: ∫_a^{s'} x + ∫_{s'}^s x = ∫_a^s x
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint' hint
  -- Key inequality: (s - s') * x(s') ≤ ∫_{s'}^s x
  suffices key : (s - s') * ℳ.x s' ≤ ∫ ψ in s'..s, ℳ.x ψ by nlinarith
  by_cases hle : s' ≤ s
  · -- Case s' ≤ s: x nondecreasing ⟹ x(ψ) ≥ x(s') on [s', s]
    have hconst : ∫ _ in s'..s, ℳ.x s' = (s - s') * ℳ.x s' := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    linarith [intervalIntegral.integral_mono_on hle intervalIntegrable_const hint
      (fun ψ hψ => ℳ.x_mono hs' ⟨le_trans hs'.1 hψ.1, le_trans hψ.2 hs.2⟩ hψ.1)]
  · -- Case s' > s: x nondecreasing ⟹ x(ψ) ≤ x(s') on [s, s']
    push_neg at hle
    have hle' := le_of_lt hle
    have hconst : ∫ _ in s..s', ℳ.x s' = (s' - s) * ℳ.x s' := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    have hmono_ineq : ∫ ψ in s..s', ℳ.x ψ ≤ ∫ _ in s..s', ℳ.x s' :=
      intervalIntegral.integral_mono_on hle' hint.symm intervalIntegrable_const
        (fun ψ hψ => ℳ.x_mono ⟨le_trans hs.1 hψ.1, le_trans hψ.2 hs'.2⟩ hs' hψ.2)
    have hsymm : ∫ ψ in s'..s, ℳ.x ψ = -(∫ ψ in s..s', ℳ.x ψ) :=
      intervalIntegral.integral_symm s s'
    nlinarith

end MyersonSufficiencySetup

end analysis

end
