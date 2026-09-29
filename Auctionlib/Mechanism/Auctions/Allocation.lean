/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Mechanism.Core.Mechanism
public import Mathlib.Algebra.Order.Group.Indicator

/-!
# Auction allocation predicates

For a mechanism `M`, `alloc o i` is bidder `i`'s allocation probability or share in outcome `o`. At
an action profile `b`, the realized allocation is `alloc (M.outcome b) i`.

`IsUnitIntervalAllocation` bounds each bidder's allocation between zero and one without restricting
the total allocation. `UsesStrictHighestBidAllocation` describes an award rule for real-valued
bids: the bidder whose bid strictly exceeds every other bid receives the whole object, and all
other bidders receive nothing. A tie for the highest bid leaves the object unallocated. This rule
is a condition on bids and allocations, not a welfare-efficiency condition.

## Main definitions

* `IsUnitIntervalAllocation`: each bidder's allocation probability or share lies in `[0, 1]`.
* `UsesStrictHighestBidAllocation`: the object goes to the unique strictly highest bidder.

## Main statements

* `UsesStrictHighestBidAllocation.isUnitIntervalAllocation`: the strict highest bid rule satisfies
  the individual allocation bounds.

## Tags

auctions, allocation, highest bid, ties
-/

@[expose] public section

namespace Auctionlib.Mechanism.Auctions

open Set

universe u v w

/-- For every action profile `b`, the mechanism `M` produces the outcome `M.outcome b`, and `alloc`
assigns each bidder `i` an allocation probability or share `alloc (M.outcome b) i` in `[0, 1]`.
This bounds individual coordinates without imposing an aggregate capacity constraint. -/
def IsUnitIntervalAllocation {I : Type u} {A : I → Type v} {O : Type w}
    (M : Mechanism I A O) (alloc : O → I → ℝ) : Prop :=
  ∀ i b, alloc (M.outcome b) i ∈ Icc 0 1

/-- For every profile `b` of real-valued bids, `alloc (M.outcome b) i` is one if and only if bidder
`i` strictly outbids every other bidder, and is zero otherwise. Thus a unique strictly highest
bidder receives the whole object, while a tie for the highest bid leaves it unallocated. This award
rule does not assert welfare efficiency. -/
def UsesStrictHighestBidAllocation {I : Type u} {O : Type w}
    (M : Mechanism I (fun _ => ℝ) O) (alloc : O → I → ℝ) : Prop :=
  ∀ i, (fun b => alloc (M.outcome b) i) = {b | ∀ j ≠ i, b j < b i}.indicator 1

/-- The strict-highest-bid rule takes coordinate values in `{0, 1}`. -/
theorem UsesStrictHighestBidAllocation.isUnitIntervalAllocation
    {I : Type u} {O : Type w} {M : Mechanism I (fun _ => ℝ) O}
    {alloc : O → I → ℝ} (h : UsesStrictHighestBidAllocation M alloc) :
    IsUnitIntervalAllocation M alloc := by
  classical
  intro i b
  change (fun b => alloc (M.outcome b) i) b ∈ Icc 0 1
  rw [h i]
  simp only [indicator_apply, mem_Icc]
  split_ifs <;> norm_num

end Auctionlib.Mechanism.Auctions
