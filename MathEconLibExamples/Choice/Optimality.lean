/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.SingleParameter.Choice
public import MathEconLib.SingleParameter.PostedPrice
public import MathEconLib.Mechanism.Choice

/-!
# Optimal selections with indifference

The posted-price problem buys at equality. Declining at equality gives the same buyer payoff and
remains universally IC, using the existing problem and its `withStrategy` operation.

For welfare, two agents favor different outcomes. Either outcome gives total value one, so both
constant mechanisms are efficient. Their distinct outcomes remain in the shared correspondence.
-/

@[expose] public section

namespace MathEconLibExamples.Choice.Optimality

open MathEconLib.Preferences
open MathEconLib MathEconLib.Choice MathEconLib.SingleParameterProblem
open MathEconLib.Mechanism

/-- Buy strictly above the price, declining when indifferent. -/
noncomputable def strictPurchase (price v : ℝ) : PurchaseDecision :=
  if price < v then .buy else .doNotBuy

/-- Changing the decision at the cutoff preserves the buyer's payoff at every type. -/
theorem strictPurchase_payoff (lo hi price v : ℝ) :
    (postedPriceProblem lo hi price).payoff v (strictPurchase price v) =
      (postedPriceProblem lo hi price).payoff v ((postedPriceProblem lo hi price).strategy v) := by
  rcases lt_trichotomy v price with h | rfl | h
  · rw [postedPriceProblem_strategy_of_lt_price lo hi price v h]
    simp [strictPurchase, not_lt_of_ge h.le]
  · simp [strictPurchase, postedPriceProblem, PurchaseDecision.allocation, PurchaseDecision.payment]
  · rw [postedPriceProblem_strategy_of_price_le lo hi price v h.le]
    simp [strictPurchase, h]

/-- Declining at equality is universally IC by feasible, payoff-preserving strategy replacement. -/
theorem strictPurchase_hasUniversalIC (lo hi price : ℝ) :
    ((postedPriceProblem lo hi price).withStrategy (strictPurchase price)).HasUniversalIC
      Set.univ :=
  (inferInstance : (postedPriceProblem lo hi price).HasUniversalIC Set.univ).withStrategy
    (strictPurchase price) (fun _ _ ↦ Set.mem_univ _)
    (fun v _ ↦ strictPurchase_payoff lo hi price v)

/-- The alternate rule selects a member of the same payoff-maximizing correspondence. -/
theorem strictPurchase_mem_maximizers (lo hi price v : ℝ) (hv : v ∈ Set.Icc lo hi) :
    strictPurchase price v ∈
      maximizers (Preference.ofUtility ((postedPriceProblem lo hi price).payoff v)) Set.univ :=
  (hasUniversalIC_iff_mem_maximizers _ _).mp (strictPurchase_hasUniversalIC lo hi price) v hv

/-- Each of two agents values their favored outcome at one and the other at zero. -/
def splitEnvironment : QuasilinearEnvironment Bool (fun _ ↦ Unit) Bool :=
  QuasilinearEnvironment.ofPrivate fun i _ o ↦ if i = o then 1 else 0

/-- Choose the specified outcome at every report profile, with no transfers. -/
def constantOutcome (o : Bool) : DirectMechanism Bool (fun _ ↦ Unit) Bool where
  outcome _ := o
  transfer _ _ := 0

/-- Either outcome yields total value one. -/
theorem splitEnvironment_totalValue (θ : Profile (fun _ : Bool ↦ Unit)) (o : Bool) :
    splitEnvironment.totalValue θ o = 1 := by
  cases o <;> norm_num [QuasilinearEnvironment.totalValue, splitEnvironment,
    QuasilinearEnvironment.ofPrivate, Fintype.sum_bool]

/-- Both outcomes belong to the welfare-maximizing correspondence. -/
theorem constantOutcome_mem_maximizers (θ : Profile (fun _ : Bool ↦ Unit)) (o : Bool) :
    (constantOutcome o).outcome θ ∈
      maximizers (Preference.ofUtility (splitEnvironment.totalValue θ)) Set.univ :=
  (mem_maximizers_ofUtility _).mpr
    ⟨Set.mem_univ _, by simp only [isMaxOn_iff, splitEnvironment_totalValue, le_refl, implies_true]⟩

/-- Selecting either tied outcome is efficient by the shared welfare bridge. -/
theorem constantOutcome_isEfficient (o : Bool) :
    DirectMechanism.IsEfficient splitEnvironment (constantOutcome o) :=
  (DirectMechanism.isEfficient_iff_mem_maximizers _ _).mpr
    fun θ ↦ constantOutcome_mem_maximizers θ o

end MathEconLibExamples.Choice.Optimality
