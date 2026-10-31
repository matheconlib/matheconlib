/-
Copyright (c) 2026 Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang, Bo Cowgill.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang, Bo Cowgill
-/
module

public import MathEconLib.Mechanism.Auctions.Allocation
public import MathEconLib.Mechanism.Core.Comap
public import MathEconLib.Mechanism.Core.SolutionConcepts
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# All-purchase specification

Bidders purchase editions at a positive posted unit price. The unique strictly highest purchaser
wins a separate prize; highest ties award no prize. Outcomes record prize shares and purchases.
The seller charges `price * b i`. Resale value `φ(B) * b i` belongs in the bidder's valuation of
the outcome, rather than in a designer-to-bidder transfer.

The paired `environment` gives utility equal to prize value plus resale value less purchase
expenditure. `netCost` is expenditure less resale value; it is not the seller's receipts.
`revenue_eq` identifies actual receipts as `price * ∑ i, b i`. Purchases remain real-valued:
nonnegative receipts require nonnegative total purchases, and global no-deficit is proved only
after restricting actions to nonnegative purchases. This accounting repair imposes no no-arbitrage
condition on the scarcity schedule and makes no equilibrium-existence claim.

Adapted from Auctionlib/Mechanism/AllPurchase.lean (commit 384acbf). The separation of receipts and
resale value follows the repair proposed by @yoshiki-pramaana in issue #239.
-/

@[expose] public section

namespace MathEconLib.Mechanism.Auctions

universe u w

/-- Posted-price all-purchase rules. The outcome exposes prize shares and purchased editions.
Resale proceeds enter `environment`, while designer transfers charge gross expenditure. -/
structure AllPurchaseSpec {I : Type u} [Fintype I] {O : Type w}
    (M : Mechanism I (fun _ ↦ ℝ) O) (alloc purchases : O → I → ℝ) where
  /-- Posted unit price. -/
  price : ℝ
  /-- The posted unit price is positive. -/
  price_pos : 0 < price
  /-- Per-edition resale value as a function of total purchases. -/
  φ : ℝ → ℝ
  /-- The scarcity schedule is continuous. -/
  φ_continuous : Continuous φ
  /-- The scarcity schedule is strictly decreasing. -/
  φ_strictAnti : StrictAnti φ
  /-- The unique strictly highest purchaser wins, with no prize awarded at highest ties. -/
  usesStrictHighestBidAllocation : UsesStrictHighestBidAllocation M alloc
  /-- The chosen outcome records each bidder's purchases. -/
  purchases_eq : ∀ b, purchases (M.outcome b) = b
  /-- Only purchase expenditure is money transferred to the designer. -/
  transfer_eq : ∀ i b, M.transfer i b = -(price * b i)

/-- Existence of posted-price all-purchase rules for these outcome projections. -/
def IsAllPurchase {I : Type u} [Fintype I] {O : Type w}
    (M : Mechanism I (fun _ ↦ ℝ) O) (alloc purchases : O → I → ℝ) : Prop :=
  Nonempty (AllPurchaseSpec M alloc purchases)

namespace AllPurchaseSpec

variable {I : Type u} [Fintype I] {O : Type w}
variable {M : Mechanism I (fun _ ↦ ℝ) O} {alloc purchases : O → I → ℝ}

/-- The bidder pays the seller the full purchase expenditure. -/
theorem payment_eq (spec : AllPurchaseSpec M alloc purchases) (i : I) (b : I → ℝ) :
    M.payment i b = spec.price * b i := by
  simp [Mechanism.payment, spec.transfer_eq]

/-- All-purchase prize allocation probabilities lie between zero and one. -/
theorem isUnitIntervalAllocation (spec : AllPurchaseSpec M alloc purchases) :
    IsUnitIntervalAllocation M alloc :=
  spec.usesStrictHighestBidAllocation.isUnitIntervalAllocation

/-- Resale proceeds are the value of the editions recorded in the outcome. -/
def resaleValue (spec : AllPurchaseSpec M alloc purchases) (o : O) (i : I) : ℝ :=
  spec.φ (∑ j, purchases o j) * purchases o i

/-- Private outcome valuations include both the prize and the purchased editions. -/
def environment (spec : AllPurchaseSpec M alloc purchases) :
    Mechanism.QuasilinearEnvironment I (fun _ ↦ ℝ) O :=
  Mechanism.QuasilinearEnvironment.ofPrivate fun i s o ↦
    s * alloc o i + spec.resaleValue o i

/-- Net cost to a bidder, including resale value, differs from the payment to the seller. -/
def netCost (spec : AllPurchaseSpec M alloc purchases) (i : I) (b : I → ℝ) : ℝ :=
  (spec.price - spec.φ (∑ j, b j)) * b i

/-- The outcome valuation restores the net-cost utility formula. -/
theorem utility_eq (spec : AllPurchaseSpec M alloc purchases) (i : I) (θ b : I → ℝ) :
    spec.environment.utility M i θ b = θ i * alloc (M.outcome b) i - spec.netCost i b := by
  simp only [environment, Mechanism.QuasilinearEnvironment.ofPrivate,
    Mechanism.QuasilinearEnvironment.utility, resaleValue, spec.purchases_eq,
    spec.transfer_eq, netCost]
  ring

/-- Actual monetary receipts equal posted price times total purchases. -/
theorem revenue_eq (spec : AllPurchaseSpec M alloc purchases) (b : I → ℝ) :
    M.revenue b = spec.price * ∑ i, b i := by
  simp [Mechanism.revenue, spec.transfer_eq, Finset.mul_sum]

/-- Nonnegative purchases give nonnegative seller receipts. -/
theorem revenue_nonnegative (spec : AllPurchaseSpec M alloc purchases) (b : I → ℝ)
    (hb : ∀ i, 0 ≤ b i) : 0 ≤ M.revenue b := by
  rw [spec.revenue_eq]
  exact mul_nonneg spec.price_pos.le (Finset.sum_nonneg fun i _ ↦ hb i)

/-- Real actions include negative purchases, so a positive price alone cannot imply no-deficit. -/
theorem not_isNoDeficit [Nonempty I] (spec : AllPurchaseSpec M alloc purchases) :
    ¬ M.IsNoDeficit := by
  classical
  intro h
  let i : I := Classical.arbitrary I
  have hn := (Mechanism.isNoDeficit_iff_revenue_nonneg M).mp h
    (fun j ↦ if j = i then -1 else 0)
  rw [spec.revenue_eq] at hn
  simp at hn
  linarith [spec.price_pos]

/-- Restricting actions to nonnegative purchases gives global no-deficit. -/
theorem isNoDeficit_nonnegative (spec : AllPurchaseSpec M alloc purchases) :
    (M.comap (fun _ (x : Set.Ici (0 : ℝ)) ↦ x.val)).IsNoDeficit := by
  rw [Mechanism.isNoDeficit_iff_revenue_nonneg]
  intro b
  exact spec.revenue_nonnegative (fun i ↦ (b i).val) (fun i ↦ (b i).property)

/-- A unit purchase identifies the posted price whenever there is a bidder. -/
theorem price_unique [Nonempty I] (spec spec' : AllPurchaseSpec M alloc purchases) :
    spec.price = spec'.price := by
  let i : I := Classical.arbitrary I
  have h := (spec.payment_eq i (fun _ ↦ 1)).symm.trans
    (spec'.payment_eq i (fun _ ↦ 1))
  simpa using h

end AllPurchaseSpec

end MathEconLib.Mechanism.Auctions
