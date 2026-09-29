/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Mechanism

/-!
# Reporting rules, payments, and incentive compatibility

For a mechanism with agents `I`, action spaces `A i`, and outcomes `O`, sequential reporting maps
compose while preserving the resulting outcomes and transfers. Payments are money paid by agents,
and revenue sums those payments. Dominant-strategy incentive compatibility compares truthful
reporting with deviations, and efficiency maximizes total value across outcomes.

A buyer with value zero or two decides whether to buy at price one. Truthful reporting maximizes
the buyer's utility and ensures nonnegative utility. A two-bidder all-purchase example constructs a
positive posted price and a continuous, strictly decreasing scarcity schedule and computes the
resulting payment. A mechanism with agents indexed by `ℕ` provides an example with Boolean actions,
a single outcome, and zero transfers.

## Main definitions

* `infiniteAgentMechanism`: a mechanism with agents indexed by `ℕ`, Boolean actions, a single
  outcome, and zero transfers.

## Main statements

* `comap_composition`: sequential reporting maps agree with their composition.
* `payment_sign` and `revenue_payments`: payments negate transfers, and revenue sums payments.
* `dsic_scope` and `efficiency_scope`: truthfulness compares reports at fixed true types, and
  efficiency maximizes total value.
* `postedPrice_isDSIC` and `postedPrice_isExPostIR`: the buyer optimally reports their type and
  obtains nonnegative utility at the posted price.
* `twoBidderAllPurchase_payment`: buying one edition each gives each bidder a net payment of four.

## Tags

mechanism design, reporting rules, transfers, revenue, incentive compatibility, welfare
-/

@[expose] public section

open Auctionlib.Mechanism Auctionlib.Mechanism.Auctions

namespace Auctionlib.Tests.Mechanism

universe uI uA uB uC uΘ uO

variable {I : Type uI} {A : I → Type uA} {B : I → Type uB} {C : I → Type uC}
variable {Θ : I → Type uΘ} {O : Type uO}

/-- Applying the reporting map `τ` and then `σ` gives the same outcome and transfers as applying
their composition. -/
lemma comap_composition (M : Mechanism I A O)
    (σ : ∀ i, B i → A i) (τ : ∀ i, C i → B i) :
    (M.comap σ).comap τ = M.comap (fun i => σ i ∘ τ i) := M.comap_comp σ τ

/-- Identity reporting preserves the entire mechanism. -/
lemma comap_identity (M : Mechanism I A O) : M.comap (fun _ => id) = M := M.comap_id

/-- Payments are money leaving the agent, so they negate the signed transfer. -/
lemma payment_sign (M : Mechanism I A O) (i : I) (a : Profile A) :
    M.payment i a = -M.transfer i a := rfl

/-- Revenue is the sum of agents' payments, with a positive payment representing money collected
from the agent. -/
lemma revenue_payments [Fintype I] (M : Mechanism I A O) (a : Profile A) :
    M.revenue a = ∑ i, M.payment i a := M.revenue_eq_sum_payment a

/-- DSIC fixes true types while allowing arbitrary reports by the other agents. -/
lemma dsic_scope [DecidableEq I] (E : QuasilinearEnvironment I Θ O)
    (M : DirectMechanism I Θ O) :
    DirectMechanism.IsDSIC E M ↔ ∀ i (θ r : Profile Θ),
      E.utility M i θ r ≤ E.utility M i θ (Function.update r i (θ i)) := Iff.rfl

/-- Efficiency requires the outcome chosen at each type profile to maximize the sum of agents'
values over all outcomes `O`. -/
lemma efficiency_scope [Fintype I] (E : QuasilinearEnvironment I Θ O)
    (M : DirectMechanism I Θ O) :
    DirectMechanism.IsEfficient E M ↔
      ∀ θ o, E.totalValue θ o ≤ E.totalValue θ (M.outcome θ) :=
  DirectMechanism.isEfficient_iff E M

/-- A mechanism is all-purchase exactly when a positive posted price and a continuous, strictly
decreasing scarcity schedule support its payment rule and its prize rule awarding the prize to the
unique highest bidder. -/
lemma allPurchase_existence [Fintype I]
    (M : Mechanism I (fun _ => ℝ) O) (alloc : O → I → ℝ) :
    IsAllPurchase M alloc ↔ Nonempty (AllPurchaseSpec M alloc) := Iff.rfl

/-- A mechanism with agents indexed by `ℕ`, Boolean actions, a single outcome, and zero
transfers. -/
def infiniteAgentMechanism : Mechanism ℕ (fun _ => Bool) Unit where
  outcome _ := ()
  transfer _ _ := 0

/-- Each agent pays zero in `infiniteAgentMechanism`, for every action profile. -/
lemma infiniteAgentMechanism_payment (i : ℕ) (a : ℕ → Bool) :
    infiniteAgentMechanism.payment i a = 0 := neg_zero

/-- One buyer reports whether their value is high and receives the good at price one exactly when
reporting high. -/
def postedPriceMechanism : Auctionlib.Mechanism Unit (fun _ => Bool) Bool where
  outcome r := r ()
  transfer _ r := if r () then -1 else 0

/-- The buyer values receiving the good at two when their type is high, and at zero otherwise. -/
def postedPriceEnvironment : QuasilinearEnvironment Unit (fun _ => Bool) Bool :=
  QuasilinearEnvironment.ofPrivate fun _ high receives =>
    if receives then if high then 2 else 0 else 0

/-- Reporting the buyer's value truthfully maximizes utility at the posted price. -/
lemma postedPrice_isDSIC :
    DirectMechanism.IsDSIC postedPriceEnvironment postedPriceMechanism := by
  intro i θ r
  cases i
  cases hθ : θ () <;> cases hr : r () <;>
    norm_num [QuasilinearEnvironment.utility, postedPriceEnvironment, postedPriceMechanism,
      QuasilinearEnvironment.ofPrivate, hθ, hr]

/-- Both low- and high-value buyers obtain nonnegative utility by reporting truthfully. -/
lemma postedPrice_isExPostIR :
    DirectMechanism.IsExPostIR postedPriceEnvironment postedPriceMechanism := by
  intro i θ
  cases i
  cases hθ : θ () <;>
    norm_num [QuasilinearEnvironment.utility, postedPriceEnvironment, postedPriceMechanism,
      QuasilinearEnvironment.ofPrivate, hθ]

/-- A high report purchases the good and charges the buyer one. -/
lemma postedPrice_purchase :
    postedPriceMechanism.outcome (fun _ => true) = true ∧
      postedPriceMechanism.payment () (fun _ => true) = 1 := by
  norm_num [postedPriceMechanism, Auctionlib.Mechanism.payment]

/-- Two bidders purchase editions at posted price two, with per-edition resale value equal to minus
aggregate purchases. The outcome records both purchase quantities. -/
noncomputable def twoBidderAllPurchase :
    Auctionlib.Mechanism (Fin 2) (fun _ => ℝ) (Fin 2 → ℝ) where
  outcome b := b
  transfer i b := -((2 - -(∑ j, b j)) * b i)

/-- The prize goes to the bidder strictly exceeding the other bidder's purchases. -/
noncomputable def twoBidderAllocation (b : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  {r | ∀ j ≠ i, r j < r i}.indicator 1 b

/-- Price two and the negative identity scarcity schedule specify the two-bidder all-purchase
mechanism. -/
noncomputable def twoBidderAllPurchaseSpec :
    AllPurchaseSpec twoBidderAllPurchase twoBidderAllocation where
  price := 2
  price_pos := by norm_num
  φ := fun total => -total
  φ_continuous := continuous_id.neg
  φ_strictAnti := fun _ _ h => neg_lt_neg h
  usesStrictHighestBidAllocation _ := rfl
  transfer_eq _ _ := rfl

/-- Each bidder's prize allocation lies in the unit interval. -/
lemma twoBidderAllPurchase_isUnitIntervalAllocation :
    IsUnitIntervalAllocation twoBidderAllPurchase twoBidderAllocation :=
  twoBidderAllPurchaseSpec.isUnitIntervalAllocation

/-- When both bidders buy one edition, each pays four after resale. -/
lemma twoBidderAllPurchase_payment (i : Fin 2) :
    twoBidderAllPurchase.payment i (fun _ => 1) = 4 := by
  rw [twoBidderAllPurchaseSpec.payment_eq]
  norm_num [twoBidderAllPurchaseSpec]

end Auctionlib.Tests.Mechanism
