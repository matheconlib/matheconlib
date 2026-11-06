/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Matching
public import Mathlib.Tactic.FinCases

/-!
# Cumulative offer boundary examples

Three contracts: proposer false prefers contract 0 to contract 2; proposer true has
contract 1. Buyer false accepts contracts 0 and 1 only together; buyer true accepts
contract 2. Sequential offers 0, 2, 1 recall contract 0, leaving infeasible held contracts.
Simultaneous offers 0 and 1 terminate immediately with feasible held contracts.

This checks that the raw cumulative offer process allows recall, that feasibility is not built in,
and that batch independence needs economic hypotheses. It uses only kernel-checked
finite decisions, not a native decision oracle.
-/

@[expose] public section

namespace MathEconLibTest.Matching.CumulativeOffer

open MathEconLib.Choice MathEconLib.Preferences
open MathEconLib.Matching.CumulativeOffer
open CumulativeOfferProcess

def buyerChoice (b : Bool) : ChoiceFunction (Fin 3) where
  toFun Y := {x | x ∈ Y ∧ if b then x = 2
    else (0 : Fin 3) ∈ Y ∧ (1 : Fin 3) ∈ Y ∧ (x = 0 ∨ x = 1)}
  choose_subset := fun _ _ hx => hx.1

@[simp] theorem buyerChoice_apply (b : Bool) (Y : Set (Fin 3)) :
    buyerChoice b Y = {x | x ∈ Y ∧ if b then x = 2
      else (0 : Fin 3) ∈ Y ∧ (1 : Fin 3) ∈ Y ∧ (x = 0 ∨ x = 1)} := rfl

def proposingSeller (x : Fin 3) : Bool := x == 1

def market : CumulativeOfferProcess Bool Bool (Fin 3) where
  buyer x := x == 2
  seller := proposingSeller
  choiceB := buyerChoice
  pref _ := CompletePreference.ofUtility
    (fun o => match o with
      | none => (0 : ℕ)
      | some x => if x.val = 2 then 1 else 2)

/-- Expose this market's numerical comparisons before enumerating dependent own contracts. -/
private theorem admissible_iff (A : Set (Fin 3)) (x : Fin 3) :
    market.Admissible A x ↔
      ∃ (s : Bool) (y : {z : Fin 3 // proposingSeller z = s}),
        y.val = x ∧ market.NoHeldContract A s ∧
          (y.val ∉ A ∧
            (0 ≤ (if y.val = 2 then 1 else 2 : ℕ) ∧
              ¬ (if y.val = 2 then 1 else 2 : ℕ) ≤ 0)) ∧
          ∀ z : {z : Fin 3 // proposingSeller z = s},
            (z.val ∉ A ∧
              (0 ≤ (if z.val = 2 then 1 else 2 : ℕ) ∧
                ¬ (if z.val = 2 then 1 else 2 : ℕ) ≤ 0)) →
            (if z.val = 2 then 1 else 2 : ℕ) ≤
              (if y.val = 2 then 1 else 2 : ℕ) := Iff.rfl

private theorem first : market.ValidBatch ∅ {0} := by
  simp only [ValidBatch, admissible_iff]
  simp [NoHeldContract, heldContracts, market, proposingSeller,
    Set.InjOn, Set.Nonempty, Subtype.exists, Subtype.forall,
    Fin.forall_fin_succ]

private theorem second : market.ValidBatch {0} {2} := by
  simp only [ValidBatch, admissible_iff]
  simp [NoHeldContract, heldContracts, market, proposingSeller,
    Set.InjOn, Set.Nonempty, Bool.exists_bool, Subtype.exists, Subtype.forall,
    Fin.forall_fin_succ]

private theorem third : market.ValidBatch ({0} ∪ {2}) {1} := by
  simp only [ValidBatch, admissible_iff]
  simp [NoHeldContract, heldContracts, market, proposingSeller,
    Set.InjOn, Set.Nonempty, Bool.exists_bool, Subtype.exists, Subtype.forall,
    Fin.forall_fin_succ]

private theorem together : market.ValidBatch ∅ {0, 1} := by
  simp only [ValidBatch, admissible_iff]
  simp [NoHeldContract, heldContracts, market, proposingSeller,
    Set.InjOn, Set.Nonempty, Subtype.exists, Subtype.forall,
    Fin.forall_fin_succ]

/-- The three singleton steps form a productive sequential history. -/
theorem sequential_run : market.Run [{1}, {2}, {0}] := by
  apply Run.cons
  · apply Run.cons
    · exact Run.cons Run.nil first
    · simpa only [offers_cons, offers_nil, Set.empty_union] using second
  · simpa only [offers_cons, offers_nil, Set.empty_union] using third

/-- The simultaneous batch is a one-round run. -/
theorem simultaneous_run : market.Run [{0, 1}] :=
  Run.cons Run.nil together

/-- Both histories are terminal, so the difference cannot be attributed to stopping early. -/
theorem both_terminal :
    market.Terminal (offers [{1}, {2}, {0}]) ∧
      market.Terminal (offers [{0, 1}]) := by
  simp [NoHeldContract, heldContracts, remaining, Eligible, Terminal, Set.Nonempty, Own,
    market, proposingSeller, offers, CompletePreference.comap, Preference.comap,
    CompletePreference.ofUtility, CompletePreference.ofPreorder,
    Preference.ofPreorder, Preference.lt,
    Bool.exists_bool, Subtype.exists, Fin.forall_fin_succ,
    Fin.exists_fin_succ]

/-- Recalling the first proposal produces two held contracts for its proposer. -/
theorem sequential_heldContracts :
    market.heldContracts (offers [{1}, {2}, {0}]) = {0, 1, 2} := by
  ext x
  fin_cases x <;> simp [heldContracts, offers, market, Bool.exists_bool]

/-- Batching the first offers prevents the second contract of proposer false from being offered. -/
theorem simultaneous_heldContracts :
    market.heldContracts (offers [{0, 1}]) = {0, 1} := by
  ext x
  fin_cases x <;> simp [heldContracts, offers, market, Bool.exists_bool]

/-- A concrete application of the generic productive-round bound. -/
example : ([{1}, {2}, {0}] : List (Set (Fin 3))).length ≤ Nat.card (Fin 3) :=
  sequential_run.length_le_card market

/-- Finite policy execution yields a terminal outcome through the public matching umbrella. -/
example (priority : LinearOrder (Fin 3)) :
    market.Outcome (market.rawOutcome (liftStatePolicy (market.fixedOrder priority))) :=
  market.rawOutcome_isOutcome ((market.fixedOrder_valid priority).lift market)

/-- Empty contracts exhaust immediately, with no assumption on buyer choice functions. -/
example (P : CumulativeOfferProcess Bool Bool Empty) : P.Terminal ∅ := by
  intro s hs
  obtain ⟨x, _⟩ := hs.2
  exact nomatch x.val


/-- A concrete policy reproduces the three-round recall history. -/
def sequentialPolicy : Policy (Fin 3) := fun h =>
  if h.length = 0 then {0} else if h.length = 1 then {2} else {1}

theorem sequential_follows : Follows sequentialPolicy [{1}, {2}, {0}] := by
  simp [Follows, sequentialPolicy]

/-- The raw outcome bridge applies even when the terminal held contracts are infeasible. -/
example : market.rawOutcome sequentialPolicy = {0, 1, 2} :=
  (sequential_run.heldContracts_eq_rawOutcome market sequential_follows
    both_terminal.1).symm.trans sequential_heldContracts

/-- A one-round policy stops early; subsequent execution leaves its terminal history intact. -/
def simultaneousPolicy : Policy (Fin 3) := fun _ => {0, 1}

theorem simultaneous_follows : Follows simultaneousPolicy [{0, 1}] := by
  simp [Follows, simultaneousPolicy]

example : market.execute simultaneousPolicy (Nat.card (Fin 3)) = [{0, 1}] :=
  simultaneous_run.execute_card_eq market simultaneous_follows both_terminal.2

example : market.rawOutcome simultaneousPolicy = {0, 1} :=
  (simultaneous_run.heldContracts_eq_rawOutcome market simultaneous_follows
    both_terminal.2).symm.trans simultaneous_heldContracts

/-- Uniqueness is policy-specific: the two concrete policies still have different outcomes. -/
example : market.rawOutcome sequentialPolicy ≠ market.rawOutcome simultaneousPolicy := by
  rw [← sequential_run.heldContracts_eq_rawOutcome market sequential_follows both_terminal.1,
    ← simultaneous_run.heldContracts_eq_rawOutcome market simultaneous_follows both_terminal.2,
    sequential_heldContracts, simultaneous_heldContracts]
  intro he
  have hx : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := he ▸ (by simp)
  simpa using hx

end MathEconLibTest.Matching.CumulativeOffer

#print axioms MathEconLib.Matching.CumulativeOffer.CumulativeOfferProcess.Run.execute_card_eq
#print axioms MathEconLib.Matching.CumulativeOffer.CumulativeOfferProcess.Run.eq_of_terminal_of_follows
#print axioms MathEconLib.Matching.CumulativeOffer.CumulativeOfferProcess.rawOutcome_eq_iff
