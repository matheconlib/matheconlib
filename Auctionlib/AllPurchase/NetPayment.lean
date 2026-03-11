module

public import Auctionlib.AllPurchase.Envelope

/-!
# All-Purchase Auction — Net-Payment Identity (Proposition 6.4)

The net-payment identity shows that the net expenditure in the all-purchase auction
equals the standard all-pay bid minus the lowest type's utility:
`C(β(v)) = allpayBid(v) - U(a)`.

## Main definitions

- `AllPurchaseCore.allpayBid`: the all-pay bid function `v · q(v) - ∫ₐᵛ q(ψ) dψ`.

## Main results

- `AllPurchaseCore.allpayBid_a`: `allpayBid(a) = a · q(a)`.
- `AllPurchaseCore.netPaymentIdentity`: `C(β(v)) = allpayBid(v) - U(a)` (Proposition 6.4).
- `AllPurchaseCore.allpayBid_nonneg`: `0 ≤ allpayBid(v)` when `0 ≤ a`.
-/

@[expose] public section

section netPayment

open MeasureTheory

namespace AllPurchaseCore

variable (ε : AllPurchaseCore)

/-- The all-pay bid function:
`allpayBid(v) = v · q(v) - ∫ₐᵛ q(ψ) dψ`.

At the economic level, `q(v) = F(v)^{n-1}` and this becomes the standard
all-pay auction equilibrium bid function. -/
noncomputable def allpayBid (v : ℝ) : ℝ :=
  v * ε.q v - ∫ ψ in ε.a..v, ε.q ψ

/-- `allpayBid(a) = a · q(a)`. Equals `0` when `a = 0` or `q(a) = 0`. -/
@[simp]
lemma allpayBid_a : ε.allpayBid ε.a = ε.a * ε.q ε.a := by
  simp [allpayBid]

/-- **Proposition 6.4 — Net-Payment Identity.**
`C(β(v)) = allpayBid(v) - U(a)` for all `v ∈ [a, b]`.

Proof: equate the equilibrium payoff definition `U(v) = v · q(v) - C(β(v))`
with the envelope condition `U(v) = U(a) + ∫ₐᵛ q(ψ) dψ` and rearrange. -/
theorem netPaymentIdentity (v : ℝ) (hv : v ∈ Set.Icc ε.a ε.b) :
    ε.C (ε.β v) = ε.allpayBid v - ε.U ε.a := by
  have hU_def : ε.U v = v * ε.q v - ε.C (ε.β v) := rfl
  have hU_rep := ε.integral_rep v hv
  have hallpay : ε.allpayBid v = v * ε.q v - ∫ ψ in ε.a..v, ε.q ψ := rfl
  linarith

/-- Non-negativity of the all-pay bid on `[a, b]` when `a ≥ 0`.

Since `q` is nondecreasing, `∫ₐᵛ q(ψ) dψ ≤ (v - a) · q(v)`,
so `allpayBid(v) ≥ a · q(v) ≥ 0`. -/
lemma allpayBid_nonneg (ha : 0 ≤ ε.a) (v : ℝ) (hv : v ∈ Set.Icc ε.a ε.b) :
    0 ≤ ε.allpayBid v := by
  simp only [allpayBid]
  have hab : ε.a ≤ ε.b := le_trans hv.1 hv.2
  have ha_mem : ε.a ∈ Set.Icc ε.a ε.b := ⟨le_refl _, hab⟩
  have hint : IntervalIntegrable ε.q volume ε.a v :=
    (ε.q_monotoneOn.mono (Set.uIcc_subset_Icc ha_mem hv)).intervalIntegrable
  have h_int_le : ∫ ψ in ε.a..v, ε.q ψ ≤ (v - ε.a) * ε.q v := by
    calc ∫ ψ in ε.a..v, ε.q ψ
      _ ≤ ∫ _ in ε.a..v, ε.q v :=
        intervalIntegral.integral_mono_on hv.1 hint intervalIntegrable_const
          fun ψ hψ => ε.q_monotoneOn (Set.Icc_subset_Icc_right hv.2 hψ) hv hψ.2
      _ = (v - ε.a) * ε.q v := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  linarith [mul_nonneg ha (ε.q_range v).1]

end AllPurchaseCore

end netPayment

end
