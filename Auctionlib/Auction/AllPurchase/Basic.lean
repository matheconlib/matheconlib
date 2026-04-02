module

public import Auctionlib.Auction.SymmetricIPV

/-!
# All-Purchase Auction (Chapter 6)

The all-purchase auction is a variation of the all-pay auction where agents
purchase units of a good ("editions") at a posted price, and the highest
purchaser wins a prize. The value of editions depends on scarcity via a
strictly decreasing function `φ`.

## Typeclass

`Mechanism.IsAllPurchase A.rules` constrains the mechanism's allocation and
payment rules to match the all-purchase format (see `Mechanism/AllPurchase.lean`).

## Definitions

- `Auction.allPayBid`: the standard all-pay bid function
  `v · F(v)^{n-1} - ∫ F(ψ)^{n-1} dψ`

The key formalized results (monotonicity, envelope, strict monotonicity,
net payment identity) are available at the `ReducedForm` / general `Auction`
level and do not depend on the all-purchase-specific parameters.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace Auction

variable (A : Auction Ω n) [HasIdenticalTypes A]

/-- The standard all-pay bid function:
`allPayBid(v) = v · F(v)^{n-1} - ∫_{lowestType}^{v} F(ψ)^{n-1} dψ`.

This is the symmetric equilibrium bid in a standard all-pay auction.
By the net-payment identity, the net expenditure in the all-purchase
auction satisfies `C(β(v)) = allPayBid(v) - U(lowestType)`. -/
noncomputable def allPayBid (v : ℝ) : ℝ :=
  v * A.commonCDF v ^ (n - 1) -
    ∫ t in A.lowestType..v, A.commonCDF t ^ (n - 1)

@[simp]
lemma allPayBid_lowestType [HasBoundedTypes A] [HasAtomlessTypes A] :
    A.allPayBid A.lowestType = 0 := by
  have hn : n - 1 ≠ 0 := by have := Nat.AtLeastTwo.prop (n := n); omega
  simp [allPayBid, zero_pow hn]

end Auction

end
