/-
Copyright (c) 2026 Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang

The all-purchase specification is adapted from Auctionlib/Mechanism/AllPurchase.lean,
introduced in commit 384acbf.
-/
module

public import MathEconLib.Mechanism.Auctions.Allocation
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# All-purchase specification

In an all-purchase mechanism, the finite type `I` indexes bidders, whose real-valued bids `b i`
represent edition purchases. The mechanism `M` determines an outcome and signed money received by
each bidder; `alloc o i` gives bidder `i`'s prize allocation at outcome `o`. The unique highest
bidder receives the prize, and tied highest bids receive no prize.

At total purchases `B = ∑ j, b j`, each edition has resale value `φ(B)`, where the scarcity
function `φ` is continuous and strictly decreasing. A positive posted unit price `p` gives bidder
`i` gross expenditure `p * b i` and net payment `(p - φ(B)) * b i` after resale. The bidder's
transfer is the negative of this net payment. Purchases and resale values are not constrained to be
nonnegative here.

## Main definitions

* `AllPurchaseSpec`: a positive posted price and a continuous, strictly decreasing resale-value
  schedule, together with the all-purchase payment and prize rules.
* `IsAllPurchase`: existence of a price and resale-value schedule satisfying the all-purchase rules.

## Main statements

* `AllPurchaseSpec.payment_eq`: net payment equals gross purchase expenditure minus resale proceeds.
* `AllPurchaseSpec.isUnitIntervalAllocation`: prize allocation probabilities lie between zero and
  one.

## Tags

all-purchase auction, posted price, scarcity, resale value, net payment, prize allocation
-/

@[expose] public section

namespace MathEconLib.Mechanism.Auctions

universe u w

/-- A posted-price and scarcity-value specification for an all-purchase mechanism `M` with finitely
many bidders `I`. Real-valued bids `b i` represent edition purchases. The mechanism determines
outcomes and signed money received by each bidder, and `alloc o i` is bidder `i`'s prize allocation
at outcome `o`.

The positive posted unit price `price` and continuous, strictly decreasing per-edition resale-value
schedule `φ` give bidder `i` gross expenditure `price * b i` and net payment
`(price - φ (∑ j, b j)) * b i`. The transfer is the negative of this net payment. The prize goes to
the unique highest bidder, with no prize awarded at ties for the highest bid. -/
structure AllPurchaseSpec {I : Type u} [Fintype I] {O : Type w}
    (M : Mechanism I (fun _ => ℝ) O) (alloc : O → I → ℝ) where
  /-- Posted unit price. -/
  price : ℝ
  /-- The posted unit price is positive. -/
  price_pos : 0 < price
  /-- Per-edition resale value as a function of total purchases. -/
  φ : ℝ → ℝ
  /-- The scarcity function is continuous. -/
  φ_continuous : Continuous φ
  /-- The scarcity function is strictly decreasing. -/
  φ_strictAnti : StrictAnti φ
  /-- The unique strictly highest bidder wins; ties for the highest bid allocate no prize. -/
  usesStrictHighestBidAllocation : UsesStrictHighestBidAllocation M alloc
  /-- Money received by bidder `i` equals resale proceeds minus gross purchase expenditure. -/
  transfer_eq : ∀ i b, M.transfer i b = -((price - φ (∑ j, b j)) * b i)

/-- There are a positive posted unit price and a continuous, strictly decreasing per-edition
resale-value schedule under which `M` pays each bidder resale proceeds minus purchase expenditure,
and `alloc` awards the prize to the unique highest bidder, with no prize awarded at ties for the
highest bid. -/
def IsAllPurchase {I : Type u} [Fintype I] {O : Type w}
    (M : Mechanism I (fun _ => ℝ) O) (alloc : O → I → ℝ) : Prop :=
  Nonempty (AllPurchaseSpec M alloc)

namespace AllPurchaseSpec

variable {I : Type u} [Fintype I] {O : Type w}
variable {M : Mechanism I (fun _ => ℝ) O} {alloc : O → I → ℝ}

/-- The bidder's net payment is gross purchase expenditure minus resale proceeds. -/
theorem payment_eq (spec : AllPurchaseSpec M alloc) (i : I) (b : I → ℝ) :
    M.payment i b = (spec.price - spec.φ (∑ j, b j)) * b i := by
  simp [Mechanism.payment, spec.transfer_eq]

/-- All-purchase prize allocation probabilities lie between zero and one. -/
theorem isUnitIntervalAllocation (spec : AllPurchaseSpec M alloc) :
    IsUnitIntervalAllocation M alloc :=
  spec.usesStrictHighestBidAllocation.isUnitIntervalAllocation

end AllPurchaseSpec

end MathEconLib.Mechanism.Auctions
