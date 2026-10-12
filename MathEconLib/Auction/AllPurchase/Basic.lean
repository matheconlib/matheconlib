module

public import MathEconLib.Auction.Typeclasses

/-!
# All-purchase payments and the all-pay bid function

In an all-purchase auction, agents purchase units of a good ("editions") at price `p` per edition.
Each edition has scarcity value `φ(B)`, strictly decreasing in total purchases `B`, so buyer `i`
makes net payment `(p - φ(B)) * b i` for `b i` editions. The strictly highest purchaser wins a
prize; a tie for the highest purchase leaves the prize unawarded.

`MathEconLib.Mechanism.Auctions.AllPurchaseSpec A.rules alloc` describes an auction with this price
and scarcity function; `IsAllPurchase` states that such parameters exist. The all-pay bid function
enters the all-purchase net-payment identity, which expresses equilibrium net expenditure as
`C(β(v)) = allPayBid(v) - U(lowestType)`.

## Sources and provenance

Scott Duke Kominers observed this all-purchase format in NFT sales; see the
[sale provenance](https://x.com/tiffatronn/status/1928904850022265170).
The economic-theory research write-up is pending. For now, cite the MathEconLib Lean development
for the formalized all-purchase analysis. The standard all-pay benchmark has separate textbook
sources, recorded alongside the all-purchase provenance in `docs/AuctionReferences.md`.

## Main definitions

* `Auction.allPayBid`: the all-pay payment expression
  `v · F(v)^{n-1} - ∫_{lowestType}^{v} F(ψ)^{n-1} dψ`.

## Main statements

* `Auction.allPayBid_lowestType`: the all-pay bid is zero at the lowest type when types are bounded
  and atomless.
* `Auction.allPayBid_measurable`: the all-pay bid function is measurable.

## Tags

all-purchase auction, all-pay auction, net expenditure
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace Auction

variable (A : Auction Ω n) [HasIdenticalTypes A]

/-- The standard all-pay bid function:
`allPayBid(v) = v · F(v)^{n-1} - ∫_{lowestType}^{v} F(ψ)^{n-1} dψ`.

This is the payment expression associated with allocation probability `F(v)^{n-1}` and zero utility
for the lowest type. The all-purchase net-payment identity expresses equilibrium net expenditure as
`C(β(v)) = allPayBid(v) - U(lowestType)`. -/
noncomputable def allPayBid (v : ℝ) : ℝ :=
  v * A.commonCDF v ^ (n - 1) -
    ∫ t in A.lowestType..v, A.commonCDF t ^ (n - 1)

/-- The all-pay bid is zero at the lowest type when types are bounded and atomless. -/
@[simp] lemma allPayBid_lowestType [HasBoundedTypes A] [HasAtomlessTypes A] :
    A.allPayBid A.lowestType = 0 := by
  have hn : n - 1 ≠ 0 := by
    have := Nat.AtLeastTwo.prop (n := n)
    omega
  simp [allPayBid, zero_pow hn]

omit [n.AtLeastTwo] in
/-- The all-pay bid function is measurable. -/
lemma allPayBid_measurable : Measurable A.allPayBid := by
  refine Measurable.sub
    (measurable_id.mul (A.commonCDF_measurable.pow measurable_const)) <|
    Monotone.measurable fun s t hst => ?_
  have hpow_mono : Monotone (fun ψ => A.commonCDF ψ ^ (n - 1)) := fun a b hab =>
    pow_le_pow_left₀ (A.commonCDF_nonneg a) (A.commonCDF_mono hab) _
  have hii1 : IntervalIntegrable (fun ψ => A.commonCDF ψ ^ (n - 1))
      volume A.lowestType s := hpow_mono.intervalIntegrable (μ := volume)
  have hii2 : IntervalIntegrable (fun ψ => A.commonCDF ψ ^ (n - 1))
      volume s t := hpow_mono.intervalIntegrable (μ := volume)
  have hadd := (intervalIntegral.integral_add_adjacent_intervals hii1 hii2).symm
  linarith [intervalIntegral.integral_nonneg (μ := volume) hst
    (fun ψ _ => pow_nonneg (A.commonCDF_nonneg ψ) (n - 1))]

end Auction

end

end MathEconLib
