/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.SingleParameter.EnvelopeIC

/-!
# Payment Identities for Single-Parameter Problems

This file states the payment side of the one-dimensional envelope theorem.
It separates three logically distinct facts:

1. envelope IC determines the payment made along the strategy;
2. two problems with the same allocation and lowest-type utility therefore
   have the same on-strategy payment;
3. conversely, a monotone allocation together with this payment formula
   implies type-deviation incentive compatibility.

These results use only the induced allocation and utility. They do not depend
on the concrete type of action chosen by the agent.
-/

namespace MathEconLib

@[expose] public section

open Set MeasureTheory

universe u v

namespace SingleParameterProblem

variable {Action : Type u} (P : SingleParameterProblem Action)

/-! ## Payment necessity and uniqueness -/

/-- **Payment identity.** Under envelope IC, the payment made by type `v`
when following the strategy is

`v * q(v) - U(lowestType) - ∫ lowestType..v, q(w) dw`.

This follows by substituting the integral representation of utility into
`U(v) = v * q(v) - payment(strategy(v))`. -/
theorem payment_identity [HasEnvelopeIC P]
    (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.payment (P.strategy v) =
      v * P.q v - P.U P.lowestType - ∫ w in P.lowestType..v, P.q w := by
  have hrep := P.integral_rep v hv
  simp only [U, payoff, q] at hrep ⊢
  linarith

/-- **Payment uniqueness.** Consider two single-parameter problems, possibly
with different action types. If they have the same type interval, induced
allocation, and lowest-type utility, then they have the same on-strategy
payment throughout the type interval. -/
theorem payment_unique [HasEnvelopeIC P]
    {OtherAction : Type v} (P₂ : SingleParameterProblem OtherAction)
    [HasEnvelopeIC P₂]
    (h_low : P.lowestType = P₂.lowestType)
    (h_high : P.highestType = P₂.highestType)
    (h_q : P.q = P₂.q)
    (h_U0 : P.U P.lowestType = P₂.U P₂.lowestType)
    (x : ℝ) (hx : x ∈ P.typeInterval) :
    P.payment (P.strategy x) = P₂.payment (P₂.strategy x) := by
  have hidentity := P.payment_identity x hx
  have hx₂ : x ∈ P₂.typeInterval := ⟨h_low ▸ hx.1, h_high ▸ hx.2⟩
  have hidentity₂ := P₂.payment_identity x hx₂
  rw [h_q, h_low] at hidentity
  rw [h_low] at h_U0
  linarith [hidentity, hidentity₂]

/-! ## Myerson sufficiency -/

/-- **Sufficiency of monotonicity and the payment identity.**

If the induced allocation is monotone and the payment made along the strategy
has the canonical integral form, then no type prefers the strategy action
assigned to another type.

The constant in the canonical payment formula is written as
`P.U P.lowestType`. This normalization makes the theorem directly converse to
`payment_identity`. -/
theorem typeDeviationIC_of_monotone_q
    (hq_mono : MonotoneOn P.q P.typeInterval)
    (hpayment : ∀ x ∈ P.typeInterval,
      P.payment (P.strategy x) =
        x * P.q x - P.U P.lowestType - ∫ w in P.lowestType..x, P.q w) :
    HasTypeDeviationIC P where
  typeDeviationIC x hx x' hx' := by
    change x * P.q x' - P.payment (P.strategy x') ≤
      x * P.q x - P.payment (P.strategy x)
    have hbounds : P.lowestType ≤ P.highestType := le_trans hx.1 hx.2
    have hlow : P.lowestType ∈ P.typeInterval := ⟨le_refl _, hbounds⟩
    have hintegrable : IntervalIntegrable P.q volume x' x :=
      (hq_mono.mono (Set.uIcc_subset_Icc hx' hx)).intervalIntegrable
    have hintegrable_low : IntervalIntegrable P.q volume P.lowestType x' :=
      (hq_mono.mono (Set.uIcc_subset_Icc hlow hx')).intervalIntegrable
    -- Split the integral at the deviating type `x'`.
    have h_integral_add := intervalIntegral.integral_add_adjacent_intervals
      hintegrable_low hintegrable
    rw [hpayment x hx, hpayment x' hx']
    -- Monotonicity bounds the integral between the two types by the
    -- rectangle with height `q(x')`. The orientation determines the sign.
    suffices hkey : (x - x') * P.q x' ≤ ∫ w in x'..x, P.q w by
      nlinarith [h_integral_add]
    by_cases hle : x' ≤ x
    · have hconst : ∫ _ in x'..x, P.q x' = (x - x') * P.q x' := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      have hmono := intervalIntegral.integral_mono_on hle intervalIntegrable_const
        hintegrable
        (fun w hw => hq_mono hx'
          ⟨le_trans hx'.1 hw.1, le_trans hw.2 hx.2⟩ hw.1)
      linarith [hconst, hmono]
    · push_neg at hle
      have hle' := le_of_lt hle
      have hconst : ∫ _ in x..x', P.q x' = (x' - x) * P.q x' := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      have hmono : ∫ w in x..x', P.q w ≤ ∫ _ in x..x', P.q x' :=
        intervalIntegral.integral_mono_on hle' hintegrable.symm
          intervalIntegrable_const
          (fun w hw => hq_mono
            ⟨le_trans hx.1 hw.1, le_trans hw.2 hx'.2⟩ hx' hw.2)
      have hsymm : ∫ w in x'..x, P.q w = -(∫ w in x..x', P.q w) :=
        intervalIntegral.integral_symm x x'
      nlinarith [hconst, hmono, hsymm]

end SingleParameterProblem

end

end MathEconLib
