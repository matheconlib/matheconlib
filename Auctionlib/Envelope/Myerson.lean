module

public import Auctionlib.Envelope.Theorem

/-!

# Myerson's Lemma

This file contains the economic formulation of Myerson's Lemma (Section 5.2),
built on the auction setup from `Auctionlib.Envelope.Theorem` and the mathematical
core from `Auctionlib.Envelope.Mathematics`.

## Definitions

- `DSIC`: dominant-strategy incentive compatibility (ex-post, strictly stronger than BIC).
- `MonotoneAlloc`: allocation rule is nondecreasing in own type for every fixed `θ_{-i}`.
- `PaymentIdentityHolds`: payment equals the canonical integral formula.

## Main results

- `myerson_necessity`: DSIC implies monotone allocation and the payment identity.
- `myerson_payment_unique`: DSIC implies payment uniqueness (given the same base utility).
- `myerson_sufficiency`: monotone allocation implies the canonical integral payment rule is DSIC.

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

/-- **Myerson's Lemma — Payment Uniqueness**: Under DSIC, the payment rule is uniquely determined
    by the allocation rule and the utility at the lowest type. -/
theorem myerson_payment_unique :
    EnvelopSetup.DSIC ≤ fun ℰ =>
      ∀ (t' : Fin ℰ.n → (Fin ℰ.n → ℝ) → ℝ),
        { ℰ with t := t' }.DSIC →
        (∀ i, ∀ θ : Fin ℰ.n → ℝ, (∀ j, θ j ∈ ℰ.interval j) →
          ℰ.t i (Function.update θ i (ℰ.θmin i)) = t' i (Function.update θ i (ℰ.θmin i))) →
        ∀ i, ∀ θ : Fin ℰ.n → ℝ, (∀ j, θ j ∈ ℰ.interval j) →
        ∀ s ∈ ℰ.interval i,
          ℰ.t i (Function.update θ i s) = t' i (Function.update θ i s) := by
  intro ℰ hdsic t' hdsic' h_base i θ hθ s hs
  have h1 := (myerson_necessity ℰ hdsic).2 i θ hθ s hs
  have h2 := (myerson_necessity { ℰ with t := t' } hdsic').2 i θ hθ s hs
  linarith [h_base i θ hθ]

/-- **Myerson's Lemma — Sufficiency**: Monotone allocation implies the canonical integral
    payment rule is DSIC. -/
theorem myerson_sufficiency :
    EnvelopSetup.MonotoneAlloc ≤ fun ℰ =>
      { ℰ with t := fun i θ => θ i * ℰ.x i θ -
        ∫ ψ in ℰ.θmin i..θ i, ℰ.x i (Function.update θ i ψ) }.DSIC := by
  intro ℰ hmono i θ hθ s' hs'
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
