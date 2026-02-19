module

public import Auctionlib.Envelope.Theorem

/-!

# Myerson's Lemma

This file contains both the mathematical core and the economic formulation of Myerson's Lemma
(Section 5.2).

## Mathematical Core

We introduce two structures mirroring the two directions of the equivalence:

- `MyersonSetUpMathsCore`: the **necessity** direction.
  Extends `EnvelopSetUpMathsCore` with a payment rule `t : ℝ → ℝ`, a DSIC condition, and a
  coherence condition `hU` tying the inherited utility `U` to the formula `U s = s * q s - t s`.
  We derive:
  1. `q` is monotone nondecreasing on `[a, b]`.
  2. The payment rule is uniquely determined (up to a constant) by the integral formula.

- `MyersonSufficiencySetup`: the **sufficiency** direction.
  Given a monotone allocation rule `x`, the canonical integral payment formula yields a DSIC
  mechanism.

## Economic Formulation

We reuse `EnvelopSetup` (probability space, bidders, allocation rule `x`, payment rule `t`).

The key new ingredient is **Dominant-Strategy Incentive Compatibility (DSIC)**: truthful
reporting must be optimal for **every** realization of the other bidders' types, not just in
expectation. This is an ex-post condition, strictly stronger than Bayesian IC.

## Main results

- `MyersonSetUpMathsCore.monotone_of_dsic`:
  DSIC implies `q` is monotone nondecreasing.
- `MyersonSetUpMathsCore.payment_identity`:
  Under DSIC, `t(s) = s · q(s) - U(a) - ∫_{a}^{s} q(ψ) dψ`.
- `MyersonSufficiencySetup.dsic_of_monotone`:
  Monotone `x` + integral payment formula ⟹ DSIC.
- `myerson_necessity`:
  DSIC ⟹ monotone allocation + payment identity.
- `myerson_sufficiency`:
  Monotone allocation ⟹ existence of DSIC payment rule.

-/

@[expose] public section

section analysis

open MeasureTheory Filter Topology Asymptotics

/-- The mathematical setup for Myerson's Lemma (necessity direction).
Extends `EnvelopSetUpMathsCore` with a payment rule and DSIC condition. -/
structure MyersonSetUpMathsCore extends EnvelopSetUpMathsCore where
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

/-- **Necessity**: DSIC implies the allocation rule is monotone nondecreasing. -/
theorem monotone_of_dsic : MonotoneOn ℳ.q (Set.Icc ℳ.a ℳ.b) :=
  ℳ.toEnvelopSetUpMathsCore.q_monotoneOn

/-- **Payment Identity**: Under DSIC, `t(s) = s · q(s) - U(a) - ∫_{a}^{s} q(ψ) dψ`. -/
theorem payment_identity (s : ℝ) (hs : s ∈ Set.Icc ℳ.a ℳ.b) :
    ℳ.t s = s * ℳ.q s - ℳ.U ℳ.a - ∫ ψ in ℳ.a..s, ℳ.q ψ := by
  have hrep := ℳ.toEnvelopSetUpMathsCore.integral_rep s hs
  have hUs := ℳ.hU s
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

section myerson

open MeasureTheory ProbabilityTheory

namespace EnvelopSetup

variable (ℰ : EnvelopSetup)

/-- Dominant-strategy incentive compatibility: truthful reporting weakly dominates all
    misreports for every realization of others' types (ex-post). -/
def DSIC : Prop :=
  ∀ i, ∀ θ : Fin ℰ.n → ℝ, (∀ j, θ j ∈ ℰ.interval j) →
    ∀ s' ∈ ℰ.interval i,
      θ i * ℰ.x i (Function.update θ i s') - ℰ.t i (Function.update θ i s') ≤
      θ i * ℰ.x i θ - ℰ.t i θ

/-- Monotone allocation: for each bidder `i` and every fixed profile of other types
(with all types in their valid ranges), the allocation `x_i(·, θ_{-i})` is nondecreasing
in `θ_i`. -/
def MonotoneAlloc : Prop :=
  ∀ i, ∀ θ : Fin ℰ.n → ℝ, (∀ j, θ j ∈ ℰ.interval j) →
    MonotoneOn (fun s => ℰ.x i (Function.update θ i s)) (ℰ.interval i)

/-- Payment identity holds: for each bidder `i` and fixed `θ_{-i}`, the payment rule equals
`t_i(s, θ_{-i}) = s · x_i(s, θ_{-i}) - U_i(θmin i, θ_{-i}) - ∫_{θmin i}^{s} x_i(ψ, θ_{-i}) dψ`. -/
def PaymentIdentityHolds : Prop :=
  ∀ i, ∀ θ : Fin ℰ.n → ℝ, (∀ j, θ j ∈ ℰ.interval j) → ∀ s ∈ ℰ.interval i,
    ℰ.t i (Function.update θ i s) =
      s * ℰ.x i (Function.update θ i s)
      - (ℰ.θmin i * ℰ.x i (Function.update θ i (ℰ.θmin i))
          - ℰ.t i (Function.update θ i (ℰ.θmin i)))
      - ∫ ψ in ℰ.θmin i..s, ℰ.x i (Function.update θ i ψ)

/-- Bridge: for a fixed profile `θ` (with all types in their intervals) and a bidder `i`,
convert the DSIC condition on the slice `x_i(·, θ_{-i})` into a `MyersonSetUpMathsCore`. -/
noncomputable def toMyersonSetUpMathsCore (i : Fin ℰ.n) (θ : Fin ℰ.n → ℝ)
    (hθ : ∀ j, θ j ∈ ℰ.interval j) (hdsic : ℰ.DSIC) : MyersonSetUpMathsCore :=
  MyersonSetUpMathsCore.mk'
    (ℰ.θmin i) (ℰ.θmax i)
    (fun s => ℰ.x i (Function.update θ i s))
    (fun s _ => ℰ.x_range i (Function.update θ i s))
    (fun s => ℰ.t i (Function.update θ i s))
    (fun s hs s' hs' => by
      have hθ' : ∀ j, Function.update θ i s j ∈ ℰ.interval j := by
        intro j
        simp only [Function.update_apply]
        split_ifs with h
        · subst h; exact hs
        · exact hθ j
      simpa using hdsic i (Function.update θ i s) hθ' s' hs')

end EnvelopSetup

end myerson

section proof

open EnvelopSetup

/-- **Myerson's Lemma — Necessity**: DSIC implies monotone allocation and the payment identity. -/
theorem myerson_necessity :
    EnvelopSetup.DSIC ≤ fun ℰ => ℰ.MonotoneAlloc ∧ ℰ.PaymentIdentityHolds := by
  intro ℰ hdsic
  constructor
  · -- Monotone allocation
    intro i θ hθ
    exact (ℰ.toMyersonSetUpMathsCore i θ hθ hdsic).monotone_of_dsic
  · -- Payment identity
    intro i θ hθ s hs
    exact (ℰ.toMyersonSetUpMathsCore i θ hθ hdsic).payment_identity s hs

/-- **Myerson's Lemma — Sufficiency**: Monotone allocation implies the existence of a DSIC
    payment rule. -/
theorem myerson_sufficiency :
    EnvelopSetup.MonotoneAlloc ≤ fun ℰ =>
      ∃ (t : Fin ℰ.n → (Fin ℰ.n → ℝ) → ℝ),
        { ℰ with t := t }.DSIC := by
  intro ℰ hmono
  -- Define canonical integral payment: t_i(θ) = θ_i·x_i(θ) - ∫_{θmin}^{θ_i} x_i(ψ,θ_{-i})dψ
  refine ⟨fun i θ => θ i * ℰ.x i θ -
    ∫ ψ in ℰ.θmin i..θ i, ℰ.x i (Function.update θ i ψ), ?_⟩
  -- Prove DSIC for this payment rule
  intro i θ hθ s' hs'
  -- Simplify Function.update nested applications in the goal
  simp only [Function.update_self, Function.update_idem]
  -- Construct the mathematical sufficiency setup for this slice
  have key := (MyersonSufficiencySetup.mk (ℰ.θmin i) (ℰ.θmax i)
    (fun s => ℰ.x i (Function.update θ i s))
    (fun s _ => ℰ.x_range i _)
    (hmono i θ hθ)).dsic_of_monotone 0 (θ i) (hθ i) s' hs'
  -- Simplify key to match the goal
  simp only [MyersonSufficiencySetup.t, sub_zero, Function.update_eq_self] at key
  linarith

end proof

end
