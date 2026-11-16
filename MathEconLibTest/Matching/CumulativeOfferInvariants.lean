/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import MathEconLib.Matching
import MathEconLibTest.Matching.CumulativeOffer

/-!
# Cumulative offer invariant clients

The positive example has two tied acceptable contracts for one proposer. The buyer
chooses every available contract, so its off-run choices are not counterparty feasible.
Nevertheless valid runs and finite policies have feasible, acceptable held contracts.
The earlier recall example witnesses the need for substitutability.
-/

open MathEconLib.Choice MathEconLib.Preferences
open MathEconLib.Matching MathEconLib.Matching.CumulativeOffer
open CumulativeOfferProcess

namespace MathEconLibTest.Matching.CumulativeOfferInvariants

def allChoice : ChoiceFunction (Fin 2) where
  toFun A := A
  choose_subset := fun _ => Set.Subset.rfl

def tied : CumulativeOfferProcess Unit Unit (Fin 2) where
  buyer _ := ()
  seller _ := ()
  choiceB _ := allChoice
  pref _ := CompletePreference.ofUtility (fun o => if o.isSome then (1 : ℕ) else 0)

theorem substitutable : ∀ b, (tied.choiceB b).Substitutable := by
  intro b x A D _ hx
  exact (hx (Set.mem_insert x A)).elim

theorem consistent : ∀ b, (tied.choiceB b).Consistent := by
  intro b A D hAD hDA
  exact Set.Subset.antisymm hDA hAD

/-- Both distinct contracts are selected off the run, despite having the same proposer. -/
theorem not_counterparty_feasible : ¬ Set.InjOn tied.seller (tied.choiceB () Set.univ) := by
  intro h
  have he : (0 : Fin 2) = 1 := h (Set.mem_univ 0) (Set.mem_univ 1) rfl
  exact (by decide : (0 : Fin 2) ≠ 1) he

theorem first_admissible : tied.Admissible ∅ 0 := by
  refine ⟨(), ⟨0, rfl⟩, rfl, ?_, ?_⟩
  · intro x hx
    exact (tied.heldContracts_subset ∅ hx).elim
  · refine ⟨⟨by simp, ?_⟩, ?_⟩
    · change (0 : ℕ) ≤ 1 ∧ ¬ (1 : ℕ) ≤ 0
      omega
    · intro y _
      change (1 : ℕ) ≤ 1
      exact le_rfl

theorem first_run : tied.Run [{0}] :=
  Run.cons Run.nil ((tied.validBatch_singleton_iff ∅ 0).2 first_admissible)

/-- The invariant applies even though the buyer fails off-run counterparty feasibility. -/
example : Set.InjOn tied.seller (tied.heldContracts (offers [{0}])) :=
  first_run.heldContracts_injOn tied substitutable

/-- Weak ties do not weaken strict acceptability relative to nonparticipation. -/
example : ∀ x ∈ tied.heldContracts (offers [{0}]), tied.Acceptable x :=
  first_run.acceptable_heldContracts tied

/-- Any valid history-dependent batch policy inherits seller feasibility. -/
example {π : Policy (Fin 2)} (hp : tied.ValidPolicy π) :
    Set.InjOn tied.seller (tied.rawOutcome π) :=
  tied.rawOutcome_injOn substitutable hp

/-- Buyer IRC is used independently of the feasibility argument. -/
example (A : Set (Fin 2)) :
    tied.choiceB () {x ∈ tied.heldContracts A | tied.buyer x = ()} =
      {x ∈ tied.heldContracts A | tied.buyer x = ()} :=
  tied.choice_heldContracts_eq consistent A ()

/-- A market whose own-menu choices accept every available contract on both sides.
The cumulative offer process still offers at most one contract for its only proposer. -/
def tiedMarket : Market Unit Unit (Fin 2) where
  buyer := tied.buyer
  seller := tied.seller
  choiceB := tied.choiceB
  choiceS _ := allChoice
  buyer_eq_of_mem := by intro b Y x _; cases b; rfl
  seller_eq_of_mem := by intro s Y x _; cases s; rfl

/-- A concrete application concludes the existing market individual-rationality predicate. -/
theorem first_indRational : tiedMarket.IndRational (tied.heldContracts (offers [{0}])) := by
  apply indRational_of_run tiedMarket tied.pref substitutable consistent ?_ ?_ first_run
  · intro s A
    cases s
    ext x
    simp [tiedMarket, Market.sellerSide, tied, allChoice]
  · intro x _
    exact Set.mem_singleton x

/-- The recalled-contract example cannot satisfy buyer substitutability. -/
example : ¬ ∀ b, (CumulativeOffer.market.choiceB b).Substitutable := by
  intro hsub
  have hf := CumulativeOffer.sequential_run.heldContracts_injOn CumulativeOffer.market hsub
  rw [CumulativeOffer.sequential_heldContracts] at hf
  have he : (0 : Fin 3) = 2 := hf (by simp) (by simp) rfl
  exact (by decide : (0 : Fin 3) ≠ 2) he

/-- The market bridge is exposed through the matching umbrella, including the same
strategy-free infinite-contract scope as the run invariant. -/
example {B S X : Type*} (M : Market B S X)
    (pref : ∀ s, CompletePreference (Option {x : X // M.seller x = s}))
    (hsub : ∀ b, (M.choiceB b).Substitutable)
    (hcons : ∀ b, (M.choiceB b).Consistent)
    (hlocal : ∀ s A, M.choiceS s (M.sellerSide s A) = M.choiceS s A)
    (haccept : ∀ x, (ofMarket M pref).Acceptable x → x ∈ M.choiceS (M.seller x) {x})
    {h : List (Set X)} (hr : (ofMarket M pref).Run h) :
    M.IndRational ((ofMarket M pref).heldContracts (offers h)) :=
  indRational_of_run M pref hsub hcons hlocal haccept hr

end MathEconLibTest.Matching.CumulativeOfferInvariants

#print axioms CumulativeOfferProcess.rejected_mono
#print axioms CumulativeOfferProcess.Run.heldContracts_injOn
#print axioms CumulativeOfferProcess.Run.acceptable_heldContracts
#print axioms indRational_of_run
#print axioms indRational_rawOutcome
#print axioms indRational_ofSellerPreferences_of_run
