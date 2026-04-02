module

public import Auctionlib.ReducedForm.EnvelopeIC

/-!
# Type-Deviation IC (Level 1)

`HasTypeDeviationIC` is the middle IC level: type `v` weakly prefers `strategy(v)`
to mimicking any other type's equilibrium bid.  This is equivalent to Myerson's DSIC
with `q = winProb ∘ strategy` and `t = cost ∘ strategy`.

## Instance chain

An instance `HasTypeDeviationIC R → HasEnvelopeIC M` is provided, so all
envelope theorem results are automatically available.

## Main results

- `Mechanism.monotone_of_typeDeviationIC`: `q` is monotone (via envelope IC).
- `Mechanism.payment_identity`: `cost(strategy(s)) = s · q(s) - U(lowestType) - ∫ q`.
- `Mechanism.payment_unique`: two mechanisms with the same `q` and `U(lowestType)` have
  the same `cost ∘ strategy`.
-/

@[expose] public section

open Set MeasureTheory

namespace ReducedForm

variable (R : ReducedForm)

/-- **Type-deviation IC** (Level 1): type `v` weakly prefers `strategy(v)` to
mimicking any other type's equilibrium bid.  Equivalent to Myerson's DSIC. -/
class HasTypeDeviationIC (R : ReducedForm) : Prop where
  typeDeviationIC : ∀ v ∈ R.typeInterval, ∀ v' ∈ R.typeInterval,
    R.payoff v (R.strategy v') ≤ R.payoff v (R.strategy v)

/-! ### Instance: Level 1 → Level 0 -/

instance {R : ReducedForm} [h : HasTypeDeviationIC R] :
    HasEnvelopeIC R where
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
theorem monotone_of_typeDeviationIC [HasTypeDeviationIC R] :
    MonotoneOn R.q R.typeInterval :=
  R.q_monotoneOn

/-- Payment identity (Myerson): under type-deviation IC,
`cost(strategy(s)) = s · q(s) - U(lowestType) - ∫ lowestType..s, q(ψ) dψ`.

This follows from the integral representation `U(s) = U(lowestType) + ∫ q`
and the definition `U(s) = s · q(s) - cost(strategy(s))`. -/
theorem payment_identity [HasTypeDeviationIC R]
    (s : ℝ) (hs : s ∈ R.typeInterval) :
    R.cost (R.strategy s) =
      s * R.q s - R.U R.lowestType - ∫ ψ in R.lowestType..s, R.q ψ := by
  have hrep := R.integral_rep s hs
  simp only [U, payoff, q, Function.comp] at hrep ⊢
  linarith

/-- Payment uniqueness: two mechanisms with the same type interval, `q`, and
`U(lowestType)` have the same `cost ∘ strategy` on the type interval. -/
theorem payment_unique [HasTypeDeviationIC R]
    (R₂ : ReducedForm) [HasTypeDeviationIC R₂]
    (h_lo : R.lowestType = R₂.lowestType) (h_hi : R.highestType = R₂.highestType)
    (h_q : R.q = R₂.q) (h_U0 : R.U R.lowestType = R₂.U R₂.lowestType)
    (s : ℝ) (hs : s ∈ R.typeInterval) :
    R.cost (R.strategy s) = R₂.cost (R₂.strategy s) := by
  have h1 := R.payment_identity s hs
  have hs₂ : s ∈ R₂.typeInterval := ⟨h_lo ▸ hs.1, h_hi ▸ hs.2⟩
  have h2 := R₂.payment_identity s hs₂
  rw [h_q, h_lo] at h1
  rw [h_lo] at h_U0
  linarith

/-! ### All-pay bid function -/

/-- The all-pay bid function:
`allPayBid(v) = v · q(v) - ∫ lowestType..v, q(ψ) dψ`.

At the economic level, `q(v) = F(v)^{n-1}` and this becomes the standard
all-pay auction equilibrium bid function. -/
noncomputable def allPayBid [HasTypeDeviationIC R] (v : ℝ) : ℝ :=
  v * R.q v - ∫ ψ in R.lowestType..v, R.q ψ

@[simp]
lemma allPayBid_lowestType [HasTypeDeviationIC R] :
    R.allPayBid R.lowestType = R.lowestType * R.q R.lowestType := by
  simp [allPayBid]

/-- **Net-payment identity** (= Proposition 6.4 in the all-purchase setting):
`cost(strategy(v)) = allPayBid(v) - U(lowestType)`.

This is a restatement of `payment_identity`. -/
theorem netPaymentIdentity [HasTypeDeviationIC R]
    (v : ℝ) (hv : v ∈ R.typeInterval) :
    R.cost (R.strategy v) = R.allPayBid v - R.U R.lowestType := by
  simp only [allPayBid]
  linarith [R.payment_identity v hv]

/-- Non-negativity of the all-pay bid when `lowestType ≥ 0`. -/
theorem allPayBid_nonneg [HasTypeDeviationIC R]
    (hlo : 0 ≤ R.lowestType) (v : ℝ) (hv : v ∈ R.typeInterval) :
    0 ≤ R.allPayBid v := by
  simp only [allPayBid]
  have hab : R.lowestType ≤ R.highestType := le_trans hv.1 hv.2
  have hlo_mem : R.lowestType ∈ R.typeInterval := ⟨le_refl _, hab⟩
  have hint : IntervalIntegrable R.q volume R.lowestType v :=
    (R.q_monotoneOn.mono (Set.uIcc_subset_Icc hlo_mem hv)).intervalIntegrable
  have h_int_le : ∫ ψ in R.lowestType..v, R.q ψ ≤ (v - R.lowestType) * R.q v :=
    calc ∫ ψ in R.lowestType..v, R.q ψ
      _ ≤ ∫ _ in R.lowestType..v, R.q v :=
        intervalIntegral.integral_mono_on hv.1 hint intervalIntegrable_const
          fun ψ hψ => R.q_monotoneOn (Set.Icc_subset_Icc_right hv.2 hψ) hv hψ.2
      _ = (v - R.lowestType) * R.q v := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  linarith [mul_nonneg hlo (R.q_range v).1]

/-! ### Myerson sufficiency

Given a mechanism with monotone `q` and cost defined by the canonical integral
formula, type-deviation IC holds. -/

/-- **Myerson sufficiency**: if `q` is monotone and `cost ∘ strategy` equals the
canonical payment formula `s · q(s) - c - ∫ q`, then type-deviation IC holds.

The constant `c` corresponds to `U(lowestType)`. -/
theorem typeDeviationIC_of_monotone_q
    (hq_mono : MonotoneOn R.q R.typeInterval)
    (hcost : ∀ s ∈ R.typeInterval,
      R.cost (R.strategy s) = s * R.q s - R.U R.lowestType -
        ∫ ψ in R.lowestType..s, R.q ψ) :
    HasTypeDeviationIC R where
  typeDeviationIC s hs s' hs' := by
    -- Goal: payoff v (strategy v') ≤ payoff v (strategy v)
    -- i.e. s * q s' - cost(strategy s') ≤ s * q s - cost(strategy s)
    show s * R.q s' - R.cost (R.strategy s') ≤ s * R.q s - R.cost (R.strategy s)
    have hab : R.lowestType ≤ R.highestType := le_trans hs.1 hs.2
    have hlo_mem : R.lowestType ∈ R.typeInterval := ⟨le_refl _, hab⟩
    -- Integrability from monotonicity
    have hint : IntervalIntegrable R.q volume s' s :=
      (hq_mono.mono (Set.uIcc_subset_Icc hs' hs)).intervalIntegrable
    have hint' : IntervalIntegrable R.q volume R.lowestType s' :=
      (hq_mono.mono (Set.uIcc_subset_Icc hlo_mem hs')).intervalIntegrable
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint' hint
    rw [hcost s hs, hcost s' hs']
    -- Key: (s - s') * q(s') ≤ ∫_{s'}^s q
    suffices key : (s - s') * R.q s' ≤ ∫ ψ in s'..s, R.q ψ by nlinarith
    by_cases hle : s' ≤ s
    · have hconst : ∫ _ in s'..s, R.q s' = (s - s') * R.q s' := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      linarith [intervalIntegral.integral_mono_on hle intervalIntegrable_const hint
        (fun ψ hψ => hq_mono hs' ⟨le_trans hs'.1 hψ.1, le_trans hψ.2 hs.2⟩ hψ.1)]
    · push_neg at hle
      have hle' := le_of_lt hle
      have hconst : ∫ _ in s..s', R.q s' = (s' - s) * R.q s' := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      have hmono_ineq : ∫ ψ in s..s', R.q ψ ≤ ∫ _ in s..s', R.q s' :=
        intervalIntegral.integral_mono_on hle' hint.symm intervalIntegrable_const
          (fun ψ hψ => hq_mono ⟨le_trans hs.1 hψ.1, le_trans hψ.2 hs'.2⟩ hs' hψ.2)
      have hsymm : ∫ ψ in s'..s, R.q ψ = -(∫ ψ in s..s', R.q ψ) :=
        intervalIntegral.integral_symm s s'
      nlinarith

end ReducedForm

end
