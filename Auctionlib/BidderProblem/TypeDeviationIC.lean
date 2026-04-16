module

public import Auctionlib.BidderProblem.EnvelopeIC

/-!
# Type-Deviation IC (Level 1)

`HasTypeDeviationIC` is the middle IC level: type `v` weakly prefers `strategy(v)`
to mimicking any other type's equilibrium bid.  This is equivalent to Myerson's DSIC
with `q = winProb ∘ strategy` and `t = cost ∘ strategy`.

## Instance chain

An instance `HasTypeDeviationIC B → HasEnvelopeIC B` is provided, so all
envelope theorem results are automatically available.

## Main results

- `BidderProblem.monotone_of_typeDeviationIC`: `q` is monotone (via envelope IC).
- `BidderProblem.payment_identity`: `cost(strategy(s)) = s · q(s) - U(lowestType) - ∫ q`.
- `BidderProblem.payment_unique`: two bidder problems with the same `q` and `U(lowestType)` have
  the same `cost ∘ strategy`.
-/

@[expose] public section

open Set MeasureTheory

namespace BidderProblem

variable (B : BidderProblem)

/-- **Type-deviation IC** (Level 1): type `v` weakly prefers `strategy(v)` to
mimicking any other type's equilibrium bid.  Equivalent to Myerson's DSIC. -/
class HasTypeDeviationIC (B : BidderProblem) : Prop where
  typeDeviationIC : ∀ v ∈ B.typeInterval, ∀ v' ∈ B.typeInterval,
    B.payoff v (B.strategy v') ≤ B.payoff v (B.strategy v)

/-! ### Instance: Level 1 → Level 0 -/

instance {B : BidderProblem} [h : HasTypeDeviationIC B] :
    HasEnvelopeIC B where
  envelopeIC s hs s' hs' := by
    have h1 := h.typeDeviationIC s hs s' hs'
    have h2 := h.typeDeviationIC s' hs' s hs
    simp only [payoff, q, U, Function.comp] at *
    nlinarith

/-! ### Myerson's Lemma (necessity direction)

Under type-deviation IC, the allocation `q` is monotone and the payment
is uniquely determined by the integral formula.
-/

/-- Necessity: type-deviation IC implies `q` is monotone. -/
theorem monotone_of_typeDeviationIC [HasTypeDeviationIC B] :
    MonotoneOn B.q B.typeInterval :=
  B.q_monotoneOn

/-- Payment identity (Myerson): under type-deviation IC,
`cost(strategy(s)) = s · q(s) - U(lowestType) - ∫ lowestType..s, q(ψ) dψ`.

This follows from the integral representation `U(s) = U(lowestType) + ∫ q`
and the definition `U(s) = s · q(s) - cost(strategy(s))`. -/
theorem payment_identity [HasTypeDeviationIC B]
    (s : ℝ) (hs : s ∈ B.typeInterval) :
    B.cost (B.strategy s) =
      s * B.q s - B.U B.lowestType - ∫ ψ in B.lowestType..s, B.q ψ := by
  have hrep := B.integral_rep s hs
  simp only [U, payoff, q, Function.comp] at hrep ⊢
  linarith

/-- Payment uniqueness: two bidder problems with the same type interval, `q`, and
`U(lowestType)` have the same `cost ∘ strategy` on the type interval. -/
theorem payment_unique [HasTypeDeviationIC B]
    (B₂ : BidderProblem) [HasTypeDeviationIC B₂]
    (h_lo : B.lowestType = B₂.lowestType) (h_hi : B.highestType = B₂.highestType)
    (h_q : B.q = B₂.q) (h_U0 : B.U B.lowestType = B₂.U B₂.lowestType)
    (s : ℝ) (hs : s ∈ B.typeInterval) :
    B.cost (B.strategy s) = B₂.cost (B₂.strategy s) := by
  have h1 := B.payment_identity s hs
  have hs₂ : s ∈ B₂.typeInterval := ⟨h_lo ▸ hs.1, h_hi ▸ hs.2⟩
  have h2 := B₂.payment_identity s hs₂
  rw [h_q, h_lo] at h1
  rw [h_lo] at h_U0
  linarith

/-! ### All-pay bid function -/

/-- The all-pay bid function:
`allPayBid(v) = v · q(v) - ∫ lowestType..v, q(ψ) dψ`.

At the economic level, `q(v) = F(v)^{n-1}` and this becomes the standard
all-pay auction equilibrium bid function. -/
noncomputable def allPayBid [HasTypeDeviationIC B] (v : ℝ) : ℝ :=
  v * B.q v - ∫ ψ in B.lowestType..v, B.q ψ

@[simp]
lemma allPayBid_lowestType [HasTypeDeviationIC B] :
    B.allPayBid B.lowestType = B.lowestType * B.q B.lowestType := by
  simp [allPayBid]

/-- **Net-payment identity** (= Proposition 6.4 in the all-purchase setting):
`cost(strategy(v)) = allPayBid(v) - U(lowestType)`.

This is a restatement of `payment_identity`. -/
theorem netPaymentIdentity [HasTypeDeviationIC B]
    (v : ℝ) (hv : v ∈ B.typeInterval) :
    B.cost (B.strategy v) = B.allPayBid v - B.U B.lowestType := by
  simp only [allPayBid]
  linarith [B.payment_identity v hv]

/-- Non-negativity of the all-pay bid when `lowestType ≥ 0`. -/
theorem allPayBid_nonneg [HasTypeDeviationIC B]
    (hlo : 0 ≤ B.lowestType) (v : ℝ) (hv : v ∈ B.typeInterval) :
    0 ≤ B.allPayBid v := by
  simp only [allPayBid]
  have hab : B.lowestType ≤ B.highestType := le_trans hv.1 hv.2
  have hlo_mem : B.lowestType ∈ B.typeInterval := ⟨le_refl _, hab⟩
  have hint : IntervalIntegrable B.q volume B.lowestType v :=
    (B.q_monotoneOn.mono (Set.uIcc_subset_Icc hlo_mem hv)).intervalIntegrable
  have h_int_le : ∫ ψ in B.lowestType..v, B.q ψ ≤ (v - B.lowestType) * B.q v :=
    calc ∫ ψ in B.lowestType..v, B.q ψ
      _ ≤ ∫ _ in B.lowestType..v, B.q v :=
        intervalIntegral.integral_mono_on hv.1 hint intervalIntegrable_const
          fun ψ hψ => B.q_monotoneOn (Set.Icc_subset_Icc_right hv.2 hψ) hv hψ.2
      _ = (v - B.lowestType) * B.q v := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  linarith [mul_nonneg hlo (B.q_range v).1]

/-! ### Myerson sufficiency

Given a bidder problem with monotone `q` and cost defined by the canonical integral
formula, type-deviation IC holds. -/

/-- **Myerson sufficiency**: if `q` is monotone and `cost ∘ strategy` equals the
canonical payment formula `s · q(s) - c - ∫ q`, then type-deviation IC holds.

The constant `c` corresponds to `U(lowestType)`. -/
theorem typeDeviationIC_of_monotone_q
    (hq_mono : MonotoneOn B.q B.typeInterval)
    (hcost : ∀ s ∈ B.typeInterval,
      B.cost (B.strategy s) = s * B.q s - B.U B.lowestType -
        ∫ ψ in B.lowestType..s, B.q ψ) :
    HasTypeDeviationIC B where
  typeDeviationIC s hs s' hs' := by
    -- Goal: payoff v (strategy v') ≤ payoff v (strategy v)
    -- i.e. s * q s' - cost(strategy s') ≤ s * q s - cost(strategy s)
    show s * B.q s' - B.cost (B.strategy s') ≤ s * B.q s - B.cost (B.strategy s)
    have hab : B.lowestType ≤ B.highestType := le_trans hs.1 hs.2
    have hlo_mem : B.lowestType ∈ B.typeInterval := ⟨le_refl _, hab⟩
    -- Integrability from monotonicity
    have hint : IntervalIntegrable B.q volume s' s :=
      (hq_mono.mono (Set.uIcc_subset_Icc hs' hs)).intervalIntegrable
    have hint' : IntervalIntegrable B.q volume B.lowestType s' :=
      (hq_mono.mono (Set.uIcc_subset_Icc hlo_mem hs')).intervalIntegrable
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint' hint
    rw [hcost s hs, hcost s' hs']
    -- Key: (s - s') * q(s') ≤ ∫_{s'}^s q
    suffices key : (s - s') * B.q s' ≤ ∫ ψ in s'..s, B.q ψ by nlinarith
    by_cases hle : s' ≤ s
    · have hconst : ∫ _ in s'..s, B.q s' = (s - s') * B.q s' := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      linarith [intervalIntegral.integral_mono_on hle intervalIntegrable_const hint
        (fun ψ hψ => hq_mono hs' ⟨le_trans hs'.1 hψ.1, le_trans hψ.2 hs.2⟩ hψ.1)]
    · push_neg at hle
      have hle' := le_of_lt hle
      have hconst : ∫ _ in s..s', B.q s' = (s' - s) * B.q s' := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      have hmono_ineq : ∫ ψ in s..s', B.q ψ ≤ ∫ _ in s..s', B.q s' :=
        intervalIntegral.integral_mono_on hle' hint.symm intervalIntegrable_const
          (fun ψ hψ => hq_mono ⟨le_trans hs.1 hψ.1, le_trans hψ.2 hs'.2⟩ hs' hψ.2)
      have hsymm : ∫ ψ in s'..s, B.q ψ = -(∫ ψ in s..s', B.q ψ) :=
        intervalIntegral.integral_symm s s'
      nlinarith

end BidderProblem

end
