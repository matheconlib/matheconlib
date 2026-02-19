module

public import Auctionlib.Envelope.Mathematics

/-!

# Myerson's Lemma (Mathematical Core)

This file contains the mathematical heart of Myerson's Lemma (Section 5.2).

We introduce two structures mirroring the two directions of the equivalence:

- `MyersonSetUpMathsCore`: the **necessity** direction.
  Given a bounded interval `[a, b]`, an allocation rule `x : ℝ → ℝ` in `[0, 1]`,
  a payment rule `t : ℝ → ℝ`, and DSIC, we derive:
  1. `x` is monotone nondecreasing on `[a, b]`.
  2. The payment rule is uniquely determined (up to a constant) by the integral formula.

- `MyersonSufficiencySetup`: the **sufficiency** direction.
  Given a monotone allocation rule `x`, the canonical integral payment formula yields a DSIC
  mechanism.

## Connection to the Envelope Theorem

The necessity direction reduces to the Envelope Theorem (`Auctionlib.Envelope.Mathematics`)
via the bridge `MyersonSetUpMathsCore.toEnvelopSetUpMathsCore`: DSIC implies the IC sandwich
lower bound, which is precisely the hypothesis of `EnvelopSetUpMathsCore`.

## Main results

- `MyersonSetUpMathsCore.monotone_of_dsic`:
  DSIC implies `x` is monotone nondecreasing.
- `MyersonSetUpMathsCore.payment_identity`:
  Under DSIC, `t(s) = s · x(s) - U(a) - ∫_{a}^{s} x(ψ) dψ`.
- `MyersonSufficiencySetup.dsic_of_monotone`:
  Monotone `x` + integral payment formula ⟹ DSIC.

-/

@[expose] public section

section analysis

open MeasureTheory Filter Topology Asymptotics

/-- The mathematical setup for Myerson's Lemma (necessity direction). -/
structure MyersonSetUpMathsCore where
  /-- lower bound -/
  a : ℝ
  /-- upper bound -/
  b : ℝ
  /-- allocation rule -/
  x : ℝ → ℝ
  /-- allocations are probabilities: x takes values in [0, 1] on [a, b] -/
  x_range : ∀ s ∈ Set.Icc a b, x s ∈ Set.Icc 0 1
  /-- payment rule -/
  t : ℝ → ℝ
  /-- Dominant-strategy incentive compatibility: for any types `s, s' ∈ [a, b]`,
      reporting truthfully (`s`) is weakly better than misreporting (`s'`). -/
  dsic : ∀ s ∈ Set.Icc a b, ∀ s' ∈ Set.Icc a b,
    s * x s' - t s' ≤ s * x s - t s

namespace MyersonSetUpMathsCore

variable (ℳ : MyersonSetUpMathsCore)

/-- Interim utility: `U(s) = s · x(s) - t(s)`. -/
noncomputable abbrev U (s : ℝ) : ℝ := s * ℳ.x s - ℳ.t s

/-- DSIC implies the IC sandwich lower bound: `(s - s') · x(s') ≤ U(s) - U(s')`. -/
lemma ic_sandwich : ∀ s ∈ Set.Icc ℳ.a ℳ.b, ∀ s' ∈ Set.Icc ℳ.a ℳ.b,
    (s - s') * ℳ.x s' ≤ ℳ.U s - ℳ.U s' := by
  intro s hs s' hs'
  have h := ℳ.dsic s hs s' hs'
  -- goal: (s - s') * x s' ≤ (s * x s - t s) - (s' * x s' - t s')
  -- which rearranges to: s * x s' - t s' ≤ s * x s - t s   (= h)
  nlinarith

/-- Bridge to `EnvelopSetUpMathsCore`, matching `ic_sandwich` to the `ic` field. -/
@[simps]
noncomputable def toEnvelopSetUpMathsCore : EnvelopSetUpMathsCore where
  a := ℳ.a
  b := ℳ.b
  q := ℳ.x
  q_range := ℳ.x_range
  U := ℳ.U
  ic := ℳ.ic_sandwich

/-- **Necessity**: DSIC implies the allocation rule is monotone nondecreasing. -/
theorem monotone_of_dsic : MonotoneOn ℳ.x (Set.Icc ℳ.a ℳ.b) := fun x hx y hy hxy => by
  rcases hxy.lt_or_eq with hlt | rfl
  · by_contra! h
    have h1 := ℳ.ic_sandwich x hx y hy
    have h2 := ℳ.ic_sandwich y hy x hx
    nlinarith [mul_pos (show 0 < y - x by linarith) (show 0 < ℳ.x x - ℳ.x y by linarith)]
  · rfl

/-- **Payment Identity**: Under DSIC, `t(s) = s · x(s) - U(a) - ∫_{a}^{s} x(ψ) dψ`. -/
theorem payment_identity (s : ℝ) (hs : s ∈ Set.Icc ℳ.a ℳ.b) :
    ℳ.t s = s * ℳ.x s - ℳ.U ℳ.a - ∫ ψ in ℳ.a..s, ℳ.x ψ := by
  have hrep := ℳ.toEnvelopSetUpMathsCore.integral_rep s hs
  simp only [toEnvelopSetUpMathsCore_U, toEnvelopSetUpMathsCore_q,
    toEnvelopSetUpMathsCore_a] at hrep
  -- hrep : ℳ.U s = ℳ.U ℳ.a + ∫ ψ in ℳ.a..s, ℳ.x ψ
  -- i.e., s * x s - t s = (a * x a - t a) + ∫ ...
  -- goal : t s = s * x s - (a * x a - t a) - ∫ ...
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

/-- **Sufficiency**: The canonical payment formula yields a DSIC mechanism. -/
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
