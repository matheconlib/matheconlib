module

public import MathEconLib.BidderProblem.EnvelopeIC
public import MathEconLib.SingleParameter.Payment

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

The public bidder statements are unchanged. Their general analytic content is
provided by `SingleParameterProblem.Payment`.
-/

namespace MathEconLib

@[expose] public section

open Set MeasureTheory

namespace BidderProblem

variable (B : BidderProblem)

/-- **Type-deviation IC** (Level 1): type `v` weakly prefers `strategy(v)` to
mimicking any other type's equilibrium bid.  Equivalent to Myerson's DSIC. -/
class HasTypeDeviationIC (B : BidderProblem) : Prop where
  typeDeviationIC : ∀ v ∈ B.typeInterval, ∀ v' ∈ B.typeInterval,
    B.payoff v (B.strategy v') ≤ B.payoff v (B.strategy v)

/-! ### Compatibility with general type-deviation IC -/

/-- Bidder type-deviation IC supplies type-deviation IC for the corresponding
general single-parameter problem. -/
instance instSingleParameterHasTypeDeviationIC
    {B : BidderProblem} [hIC : HasTypeDeviationIC B] :
    SingleParameterProblem.HasTypeDeviationIC B.toSingleParameterProblem where
  typeDeviationIC v hv v' hv' := by
    simpa using hIC.typeDeviationIC v hv v' hv'

/-- Conversely, general type-deviation IC for the converted problem supplies
the original bidder type-deviation IC condition. -/
theorem hasTypeDeviationIC_of_toSingleParameterProblem
    {B : BidderProblem}
    (hIC : SingleParameterProblem.HasTypeDeviationIC B.toSingleParameterProblem) :
    HasTypeDeviationIC B where
  typeDeviationIC v hv v' hv' := by
    simpa using hIC.typeDeviationIC v hv v' hv'

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
  simpa using B.toSingleParameterProblem.payment_identity s hs

/-- Payment uniqueness: two bidder problems with the same type interval, `q`, and
`U(lowestType)` have the same `cost ∘ strategy` on the type interval. -/
theorem payment_unique [HasTypeDeviationIC B]
    (B₂ : BidderProblem) [HasTypeDeviationIC B₂]
    (h_lo : B.lowestType = B₂.lowestType) (h_hi : B.highestType = B₂.highestType)
    (h_q : B.q = B₂.q) (h_U0 : B.U B.lowestType = B₂.U B₂.lowestType)
    (s : ℝ) (hs : s ∈ B.typeInterval) :
    B.cost (B.strategy s) = B₂.cost (B₂.strategy s) := by
  simpa using B.toSingleParameterProblem.payment_unique
    B₂.toSingleParameterProblem h_lo h_hi h_q h_U0 s hs

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
    HasTypeDeviationIC B := by
  have hgeneral :
      SingleParameterProblem.HasTypeDeviationIC B.toSingleParameterProblem :=
    SingleParameterProblem.typeDeviationIC_of_monotone_q
      B.toSingleParameterProblem
      (by simpa using hq_mono)
      (by
        intro s hs
        simpa using hcost s hs)
  exact hasTypeDeviationIC_of_toSingleParameterProblem hgeneral

end BidderProblem

end

end MathEconLib
