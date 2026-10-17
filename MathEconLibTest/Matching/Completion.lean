/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import MathEconLib.Matching
import MathEconLibTest.Choice.CompletionCounterexamples

/-!
# Completion-transfer regression checks

The public matching umbrella must expose the reduction. Reuse the existing
three-contract counterexample, whose original buyer is not unilaterally
substitutable and whose completion is not a pointwise enlargement. Add
unit-demand sellers to exercise stable existence in an actual market.
The false seller ranks `a` above `b`; the true seller accepts `c`.
-/

namespace MathEconLibTest.Matching.Completion

open MathEconLib.Choice MathEconLib.Matching
open ChoiceFunction.Counterexamples.Completion
open Contract

/-- Two sellers, with the first choosing `a` before `b`. -/
def sellerChoice (s : Bool) : ChoiceFunction Contract where
  toFun Y := {x | match x with
    | a => s = false ∧ a ∈ Y
    | b => s = false ∧ b ∈ Y ∧ a ∉ Y
    | c => s = true ∧ c ∈ Y}
  choose_subset Y x hx := by
    cases x with
    | a => exact hx.2
    | b => exact hx.2.1
    | c => exact hx.2

theorem sellerChoice_unitDemand (s : Bool) : (sellerChoice s).UnitDemand := by
  intro Y x hx y hy
  cases x <;> cases y <;> simp_all [sellerChoice]

theorem sellerChoice_consistent (s : Bool) : (sellerChoice s).Consistent := by
  intro Y Z hCY hZY
  have ha := @hCY a
  have hb := @hCY b
  have hc := @hCY c
  have hza := @hZY a
  have hzb := @hZY b
  have hzc := @hZY c
  simp only [sellerChoice] at ha hb hc
  clear hCY hZY
  ext x
  cases x <;> simp only [sellerChoice] <;> tauto

def market : Market Unit Bool Contract where
  buyer := fun _ => ()
  seller := counterparty
  choiceB := fun _ => original
  choiceS := sellerChoice
  buyer_eq_of_mem := by intros; exact Subsingleton.elim _ _
  seller_eq_of_mem := by
    intro s Y x hx
    cases x <;> exact hx.1.symm

theorem market_unitDemand : market.SellersUnitDemand := sellerChoice_unitDemand

theorem market_consistent : market.Consistent :=
  ⟨fun _ => original_consistent, sellerChoice_consistent⟩

theorem market_feasibleChoices : market.BuyersCounterpartyFeasible :=
  fun _ => original_feasible

/-- Apply the existence reduction to a non-substitutable original buyer. -/
theorem exists_stable :
    ∃ A : Set Contract, market.Stable A ∧ market.ManyToOneFeasible A :=
  market.exists_stable_of_buyerCompletions market_unitDemand market_consistent
    (fun _ => original_hasConsistentSubstitutableCompletion)

/-- This application cannot be reduced to the unilateral-substitutes corollary. -/
example : ¬ market.BuyersUnilaterallySubstitutable :=
  fun h => original_not_unilaterallySubstitutable (h ())

/-- Nor can the transfer theorem assume that completion enlarges choices. -/
example : ¬ original ≤ completed := completed_not_enlargement

/-- An explicit completed-market certificate transfers through the public API. -/
example {A : Set Contract}
    (hA : (market.withBuyerCompletions (fun _ => completed)
      (fun _ => isCompletionOf) (fun _ => completed_substitutable)).Stable A) :
    market.Stable A :=
  market.stable_of_withBuyerCompletions (fun _ => completed)
    (fun _ => isCompletionOf) (fun _ => completed_substitutable)
    market_unitDemand market_consistent (fun _ => completed_consistent) hA

/-- The completed market selects both sellers at their preferred available
contracts. This is a concrete certificate, not only an existence assertion. -/
theorem stable_completed_ac :
    (market.withBuyerCompletions (fun _ => completed)
      (fun _ => isCompletionOf) (fun _ => completed_substitutable)).Stable {a, c} := by
  let N := market.withBuyerCompletions (fun _ => completed)
    (fun _ => isCompletionOf) (fun _ => completed_substitutable)
  apply Market.PairwiseStable.stable_of_substitutable N
    ⟨fun _ => completed_substitutable,
      fun s => (sellerChoice_unitDemand s).substitutable (sellerChoice_consistent s)⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro b
    ext x
    cases x <;> simp [N, market, Market.withBuyerCompletions, Market.buyerSide]
  · intro s
    ext x
    cases s <;> cases x <;>
      simp [N, market, Market.withBuyerCompletions, Market.sellerSide,
        sellerChoice, counterparty]
  · intro z
    rw [N.blocks_singleton_iff]
    cases z <;>
      simp [N, market, Market.withBuyerCompletions, sellerChoice, counterparty]

/-- Transfer the explicit two-seller outcome to the non-substitutable market. -/
theorem stable_ac : market.Stable {a, c} :=
  market.stable_of_withBuyerCompletions (fun _ => completed)
    (fun _ => isCompletionOf) (fun _ => completed_substitutable)
    market_unitDemand market_consistent (fun _ => completed_consistent) stable_completed_ac

/-- A client can construct markets directly from sellers' strict preferences. -/
example {B S X : Type*} [Finite X] (buyer : X → B) (seller : X → S)
    (C : B → ChoiceFunction X)
    (hsupport : ∀ ⦃b Y x⦄, x ∈ C b Y → buyer x = b)
    (pref : ∀ s, LinearOrder (Option {x : X // seller x = s}))
    (hIRC : ∀ b, (C b).Consistent)
    (hcomp : ∀ b, (C b).HasConsistentSubstitutableCompletion seller) :
    ∃ A, (Market.ofSellerPreferences buyer seller C hsupport pref).Stable A ∧
      Set.InjOn seller A := by
  apply Market.exists_stable_of_buyerCompletions
    (Market.ofSellerPreferences buyer seller C hsupport pref)
  · exact Market.sellersUnitDemand_ofSellerPreferences buyer seller C hsupport pref
  · exact ⟨hIRC, Market.consistent_choiceS_ofSellerPreferences buyer seller C hsupport pref⟩
  · exact hcomp

#print axioms Market.stable_of_withBuyerCompletions
#print axioms Market.exists_stable_of_buyerCompletions
#print axioms Market.exists_stable_of_buyersUnilaterallySubstitutable_of_finiteValued
#print axioms Market.exists_stable_of_buyersUnilaterallySubstitutable
#print axioms exists_stable
#print axioms stable_ac

end MathEconLibTest.Matching.Completion
