module

public import Auctionlib.Envelope.Theorem
public import Auctionlib.Myerson.Mathematics

/-!

# Myerson's Lemma (Economic Formulation)

This file applies the mathematical results from `Auctionlib.Myerson.Mathematics` to the
standard single-parameter auction model from `Auctionlib.Envelope.Theorem`.

## Setup

We reuse `EnvelopSetup` (probability space, bidders, allocation rule `x`, payment rule `t`).

The key new ingredient is **Dominant-Strategy Incentive Compatibility (DSIC)**: truthful
reporting must be optimal for **every** realization of the other bidders' types, not just in
expectation. This is an ex-post condition, strictly stronger than Bayesian IC.

## Main results

- `myerson_necessity`:
  DSIC ⟹ for each bidder `i` and fixed `θ_{-i}`, the slice `x_i(·, θ_{-i})` is
  monotone nondecreasing in `θ_i`, and the payment is given by the integral formula.
- `myerson_sufficiency`:
  If every slice `x_i(·, θ_{-i})` is monotone, then the integral payment formula defines a
  DSIC mechanism.

## Connection to the Envelope Theorem

The necessity direction goes through `toMyersonSetUpMathsCore`, which reduces each
fixed-`θ_{-i}` slice to a `MyersonSetUpMathsCore` problem. The latter bridges to
`EnvelopSetUpMathsCore`, where the full analytic machinery is available.

-/

@[expose] public section

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
@[simps]
noncomputable def toMyersonSetUpMathsCore (i : Fin ℰ.n) (θ : Fin ℰ.n → ℝ)
    (hθ : ∀ j, θ j ∈ ℰ.interval j) (hdsic : ℰ.DSIC) : MyersonSetUpMathsCore where
  a := ℰ.θmin i
  b := ℰ.θmax i
  x := fun s => ℰ.x i (Function.update θ i s)
  x_range := fun s _ => ℰ.x_range i (Function.update θ i s)
  t := fun s => ℰ.t i (Function.update θ i s)
  dsic := fun s hs s' hs' => by
    have hθ' : ∀ j, Function.update θ i s j ∈ ℰ.interval j := by
      intro j
      simp only [Function.update_apply]
      split_ifs with h
      · subst h; exact hs
      · exact hθ j
    simpa using hdsic i (Function.update θ i s) hθ' s' hs'

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
