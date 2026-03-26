module

public import Auctionlib.Mechanism.EnvelopeIC

/-!
# Type-Deviation IC (Level 1)

`HasTypeDeviationIC` is the middle IC level: type `v` weakly prefers `strategy(v)`
to mimicking any other type's equilibrium bid.  This is equivalent to Myerson's DSIC
with `q = winProb ∘ strategy` and `t = cost ∘ strategy`.

## Instance chain

An instance `HasTypeDeviationIC M → HasEnvelopeIC M` is provided, so all
envelope theorem results are automatically available.

## Main results

- `Mechanism.monotone_of_typeDeviationIC`: `q` is monotone (via envelope IC).
- `Mechanism.payment_identity`: `cost(strategy(s)) = s · q(s) - U(lowestType) - ∫ q`.
- `Mechanism.payment_unique`: two mechanisms with the same `q` and `U(lowestType)` have
  the same `cost ∘ strategy`.
-/

@[expose] public section

open Set MeasureTheory

namespace Mechanism

variable (M : Mechanism)

/-- **Type-deviation IC** (Level 1): type `v` weakly prefers `strategy(v)` to
mimicking any other type's equilibrium bid.  Equivalent to Myerson's DSIC. -/
class HasTypeDeviationIC (M : Mechanism) : Prop where
  typeDeviationIC : ∀ v ∈ M.typeInterval, ∀ v' ∈ M.typeInterval,
    M.payoff v (M.strategy v') ≤ M.payoff v (M.strategy v)

/-! ### Instance: Level 1 → Level 0 -/

instance {M : Mechanism} [h : HasTypeDeviationIC M] :
    HasEnvelopeIC M where
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
theorem monotone_of_typeDeviationIC [HasTypeDeviationIC M] :
    MonotoneOn M.q M.typeInterval :=
  M.q_monotoneOn

/-- Payment identity (Myerson): under type-deviation IC,
`cost(strategy(s)) = s · q(s) - U(lowestType) - ∫ lowestType..s, q(ψ) dψ`.

This follows from the integral representation `U(s) = U(lowestType) + ∫ q`
and the definition `U(s) = s · q(s) - cost(strategy(s))`. -/
theorem payment_identity [HasTypeDeviationIC M]
    (s : ℝ) (hs : s ∈ M.typeInterval) :
    M.cost (M.strategy s) =
      s * M.q s - M.U M.lowestType - ∫ ψ in M.lowestType..s, M.q ψ := by
  have hrep := M.integral_rep s hs
  simp only [U, payoff, q, Function.comp] at hrep ⊢
  linarith

/-- Payment uniqueness: two mechanisms with the same type interval, `q`, and
`U(lowestType)` have the same `cost ∘ strategy` on the type interval. -/
theorem payment_unique [HasTypeDeviationIC M]
    (M₂ : Mechanism) [HasTypeDeviationIC M₂]
    (h_lo : M.lowestType = M₂.lowestType) (h_hi : M.highestType = M₂.highestType)
    (h_q : M.q = M₂.q) (h_U0 : M.U M.lowestType = M₂.U M₂.lowestType)
    (s : ℝ) (hs : s ∈ M.typeInterval) :
    M.cost (M.strategy s) = M₂.cost (M₂.strategy s) := by
  have h1 := M.payment_identity s hs
  have hs₂ : s ∈ M₂.typeInterval := ⟨h_lo ▸ hs.1, h_hi ▸ hs.2⟩
  have h2 := M₂.payment_identity s hs₂
  rw [h_q, h_lo] at h1
  rw [h_lo] at h_U0
  linarith

/-! ### All-pay bid function -/

/-- The all-pay bid function:
`allpayBid(v) = v · q(v) - ∫ lowestType..v, q(ψ) dψ`.

At the economic level, `q(v) = F(v)^{n-1}` and this becomes the standard
all-pay auction equilibrium bid function. -/
noncomputable def allpayBid [HasTypeDeviationIC M] (v : ℝ) : ℝ :=
  v * M.q v - ∫ ψ in M.lowestType..v, M.q ψ

@[simp]
lemma allpayBid_lowestType [HasTypeDeviationIC M] :
    M.allpayBid M.lowestType = M.lowestType * M.q M.lowestType := by
  simp [allpayBid]

/-- **Net-payment identity** (= Proposition 6.4 in the all-purchase setting):
`cost(strategy(v)) = allpayBid(v) - U(lowestType)`.

This is a restatement of `payment_identity`. -/
theorem netPaymentIdentity [HasTypeDeviationIC M]
    (v : ℝ) (hv : v ∈ M.typeInterval) :
    M.cost (M.strategy v) = M.allpayBid v - M.U M.lowestType := by
  simp only [allpayBid]
  linarith [M.payment_identity v hv]

/-- Non-negativity of the all-pay bid when `lowestType ≥ 0`. -/
theorem allpayBid_nonneg [HasTypeDeviationIC M]
    (hlo : 0 ≤ M.lowestType) (v : ℝ) (hv : v ∈ M.typeInterval) :
    0 ≤ M.allpayBid v := by
  simp only [allpayBid]
  have hab : M.lowestType ≤ M.highestType := le_trans hv.1 hv.2
  have hlo_mem : M.lowestType ∈ M.typeInterval := ⟨le_refl _, hab⟩
  have hint : IntervalIntegrable M.q volume M.lowestType v :=
    (M.q_monotoneOn.mono (Set.uIcc_subset_Icc hlo_mem hv)).intervalIntegrable
  have h_int_le : ∫ ψ in M.lowestType..v, M.q ψ ≤ (v - M.lowestType) * M.q v :=
    calc ∫ ψ in M.lowestType..v, M.q ψ
      _ ≤ ∫ _ in M.lowestType..v, M.q v :=
        intervalIntegral.integral_mono_on hv.1 hint intervalIntegrable_const
          fun ψ hψ => M.q_monotoneOn (Set.Icc_subset_Icc_right hv.2 hψ) hv hψ.2
      _ = (v - M.lowestType) * M.q v := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  linarith [mul_nonneg hlo (M.q_range v).1]

/-! ### Myerson sufficiency

Given a mechanism with monotone `q` and cost defined by the canonical integral
formula, type-deviation IC holds. -/

/-- **Myerson sufficiency**: if `q` is monotone and `cost ∘ strategy` equals the
canonical payment formula `s · q(s) - c - ∫ q`, then type-deviation IC holds.

The constant `c` corresponds to `U(lowestType)`. -/
theorem typeDeviationIC_of_monotone_q
    (hq_mono : MonotoneOn M.q M.typeInterval)
    (hcost : ∀ s ∈ M.typeInterval,
      M.cost (M.strategy s) = s * M.q s - M.U M.lowestType -
        ∫ ψ in M.lowestType..s, M.q ψ) :
    HasTypeDeviationIC M where
  typeDeviationIC s hs s' hs' := by
    -- Goal: payoff v (strategy v') ≤ payoff v (strategy v)
    -- i.e. s * q s' - cost(strategy s') ≤ s * q s - cost(strategy s)
    show s * M.q s' - M.cost (M.strategy s') ≤ s * M.q s - M.cost (M.strategy s)
    have hab : M.lowestType ≤ M.highestType := le_trans hs.1 hs.2
    have hlo_mem : M.lowestType ∈ M.typeInterval := ⟨le_refl _, hab⟩
    -- Integrability from monotonicity
    have hint : IntervalIntegrable M.q volume s' s :=
      (hq_mono.mono (Set.uIcc_subset_Icc hs' hs)).intervalIntegrable
    have hint' : IntervalIntegrable M.q volume M.lowestType s' :=
      (hq_mono.mono (Set.uIcc_subset_Icc hlo_mem hs')).intervalIntegrable
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint' hint
    rw [hcost s hs, hcost s' hs']
    -- Key: (s - s') * q(s') ≤ ∫_{s'}^s q
    suffices key : (s - s') * M.q s' ≤ ∫ ψ in s'..s, M.q ψ by nlinarith
    by_cases hle : s' ≤ s
    · have hconst : ∫ _ in s'..s, M.q s' = (s - s') * M.q s' := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      linarith [intervalIntegral.integral_mono_on hle intervalIntegrable_const hint
        (fun ψ hψ => hq_mono hs' ⟨le_trans hs'.1 hψ.1, le_trans hψ.2 hs.2⟩ hψ.1)]
    · push_neg at hle
      have hle' := le_of_lt hle
      have hconst : ∫ _ in s..s', M.q s' = (s' - s) * M.q s' := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      have hmono_ineq : ∫ ψ in s..s', M.q ψ ≤ ∫ _ in s..s', M.q s' :=
        intervalIntegral.integral_mono_on hle' hint.symm intervalIntegrable_const
          (fun ψ hψ => hq_mono ⟨le_trans hs.1 hψ.1, le_trans hψ.2 hs'.2⟩ hs' hψ.2)
      have hsymm : ∫ ψ in s'..s, M.q ψ = -(∫ ψ in s..s', M.q ψ) :=
        intervalIntegral.integral_symm s s'
      nlinarith

end Mechanism

end
