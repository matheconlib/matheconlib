/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.SingleParameter.Payment
import Mathlib.Tactic.Linarith

/-!
# A Fixed Posted Price as a Single-Parameter Problem

This file gives the first concrete pricing application of
`SingleParameterProblem`.

A buyer has a real-valued type `v` but only two possible actions:

* `buy`, which gives allocation `1` and requires payment of the posted price;
* `doNotBuy`, which gives allocation `0` and requires no payment.

At price `p`, buying gives payoff `v - p`, while not buying gives payoff `0`.
The strategy therefore buys exactly when `p ≤ v`. At the tie `p = v`, this
file chooses `buy`; either action would be optimal.

The example is deliberately deterministic. It introduces neither a type
distribution nor a seller objective. Those belong to the next layer of the
pricing development.
-/

namespace MathEconLib

@[expose] public section

open Set

namespace SingleParameterProblem

/-! ## Purchase decisions -/

/-- The two actions available to a buyer facing a fixed posted price. -/
inductive PurchaseDecision where
  /-- Purchase the object at the posted price. -/
  | buy
  /-- Decline to purchase the object. -/
  | doNotBuy
  deriving DecidableEq

namespace PurchaseDecision

/-- Allocation produced by a purchase decision. -/
def allocation : PurchaseDecision → ℝ
  | buy => 1
  | doNotBuy => 0

/-- Payment produced by a purchase decision at price `price`. -/
def payment (price : ℝ) : PurchaseDecision → ℝ
  | buy => price
  | doNotBuy => 0

end PurchaseDecision

/-! ## The buyer's problem -/

/-- The deterministic problem faced by a buyer at a fixed posted price.

The buyer's type lies in `[lowestType, highestType]`. The action space has two
elements even though the type interval generally contains infinitely many
possible types.

The `noncomputable` keyword allows the strategy to use classical comparison
of arbitrary real numbers. It does not add an economic assumption. -/
noncomputable def postedPriceProblem
    (lowestType highestType price : ℝ) :
    SingleParameterProblem PurchaseDecision where
  lowestType := lowestType
  highestType := highestType
  allocation := PurchaseDecision.allocation
  allocation_range decision := by
    cases decision <;> simp [PurchaseDecision.allocation]
  payment := PurchaseDecision.payment price
  strategy v := if price ≤ v then .buy else .doNotBuy

@[simp]
lemma postedPriceProblem_payoff_buy
    (lowestType highestType price v : ℝ) :
    (postedPriceProblem lowestType highestType price).payoff
      v .buy = v - price := by
  simp [postedPriceProblem, payoff, PurchaseDecision.allocation,
    PurchaseDecision.payment]

@[simp]
lemma postedPriceProblem_payoff_doNotBuy
    (lowestType highestType price v : ℝ) :
    (postedPriceProblem lowestType highestType price).payoff
      v .doNotBuy = 0 := by
  simp [postedPriceProblem, payoff, PurchaseDecision.allocation,
    PurchaseDecision.payment]

/-- A buyer whose value is at least the price chooses to buy. -/
lemma postedPriceProblem_strategy_of_price_le
    (lowestType highestType price v : ℝ) (hprice : price ≤ v) :
    (postedPriceProblem lowestType highestType price).strategy v =
      .buy := by
  simp [postedPriceProblem, hprice]

/-- A buyer whose value is below the price chooses not to buy. -/
lemma postedPriceProblem_strategy_of_lt_price
    (lowestType highestType price v : ℝ) (hprice : v < price) :
    (postedPriceProblem lowestType highestType price).strategy v =
      .doNotBuy := by
  simp [postedPriceProblem, not_le.mpr hprice]

/-- The induced allocation is `1` when the buyer's value reaches the price and
`0` otherwise. -/
lemma postedPriceProblem_q
    (lowestType highestType price v : ℝ) :
    (postedPriceProblem lowestType highestType price).q v =
      if price ≤ v then 1 else 0 := by
  by_cases hprice : price ≤ v <;>
    simp [postedPriceProblem, q, PurchaseDecision.allocation, hprice]

/-- The buyer's utility is `v - price` when purchasing and `0` otherwise. -/
lemma postedPriceProblem_U
    (lowestType highestType price v : ℝ) :
    (postedPriceProblem lowestType highestType price).U v =
      if price ≤ v then v - price else 0 := by
  by_cases hprice : price ≤ v <;>
    simp [postedPriceProblem, U, payoff, PurchaseDecision.allocation,
      PurchaseDecision.payment, hprice]

/-! ## Optimality and participation -/

/-- The threshold strategy is universally incentive compatible over the two
purchase decisions. -/
instance instHasUniversalICPostedPriceProblem
    (lowestType highestType price : ℝ) :
    HasUniversalIC
      (postedPriceProblem lowestType highestType price)
      (Set.univ : Set PurchaseDecision) where
  strategyInS _ _ := Set.mem_univ _
  universalIC v _ decision _ := by
    by_cases hprice : price ≤ v
    · cases decision <;>
        simp [postedPriceProblem, payoff, PurchaseDecision.allocation,
          PurchaseDecision.payment, hprice]
    · have hv_lt_price : v < price := lt_of_not_ge hprice
      cases decision with
      | buy =>
        simp [postedPriceProblem, payoff, PurchaseDecision.allocation,
          PurchaseDecision.payment, hprice]
        linarith
      | doNotBuy =>
        simp [postedPriceProblem, payoff, PurchaseDecision.allocation,
          PurchaseDecision.payment, hprice]

/-- The generic IC implication chain and envelope theorem show that demand is
monotone in the buyer's value. -/
theorem postedPriceProblem_q_monotoneOn
    (lowestType highestType price : ℝ) :
    MonotoneOn
      (postedPriceProblem lowestType highestType price).q
      (postedPriceProblem lowestType highestType price).typeInterval :=
  (postedPriceProblem lowestType highestType price).q_monotoneOn

/-- The option not to buy makes the fixed posted-price problem individually
rational for every type interval and every price. -/
theorem postedPriceProblem_isIndividuallyRational
    (lowestType highestType price : ℝ) :
    (postedPriceProblem lowestType highestType price).IsIndividuallyRational := by
  intro v _
  rw [postedPriceProblem_U]
  split_ifs with hprice
  · linarith
  · exact le_refl 0

/-- If the lowest type does not exceed the price, then its utility is zero. -/
theorem postedPriceProblem_hasZeroLowestTypeUtility
    (lowestType highestType price : ℝ) (hprice : lowestType ≤ price) :
    (postedPriceProblem lowestType highestType price).HasZeroLowestTypeUtility := by
  unfold HasZeroLowestTypeUtility
  change (postedPriceProblem lowestType highestType price).U lowestType = 0
  rw [postedPriceProblem_U]
  by_cases hbuy : price ≤ lowestType
  · rw [ite_eq_left hbuy]
    linarith
  · simp [hbuy]

end SingleParameterProblem

end

end MathEconLib
