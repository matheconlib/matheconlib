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
contract 2. Sequential offers 0, 2, 1 recall contract 0, leaving infeasible holdings.
Simultaneous offers 0 and 1 terminate immediately with feasible holdings.

This checks that the raw process allows recall, that feasibility is not built in,
and that batch independence needs economic hypotheses. It uses only kernel-checked
finite decisions, not a native decision oracle.
-/

@[expose] public section

namespace MathEconLibTest.Matching.CumulativeOffer

open MathEconLib.Choice MathEconLib.Preferences
open MathEconLib.Matching.CumulativeOffer
open Process

def receiving (b : Bool) : ChoiceFunction (Fin 3) where
  toFun Y := {x | x ∈ Y ∧ if b then x = 2
    else (0 : Fin 3) ∈ Y ∧ (1 : Fin 3) ∈ Y ∧ (x = 0 ∨ x = 1)}
  choose_subset := fun _ _ hx => hx.1

@[simp] theorem receiving_apply (b : Bool) (Y : Set (Fin 3)) :
    receiving b Y = {x | x ∈ Y ∧ if b then x = 2
      else (0 : Fin 3) ∈ Y ∧ (1 : Fin 3) ∈ Y ∧ (x = 0 ∨ x = 1)} := rfl

def owner (x : Fin 3) : Bool := x == 1

def market : Process Bool Bool (Fin 3) where
  buyer x := x == 2
  seller := owner
  choiceB := receiving
  pref _ := CompletePreference.ofUtility
    (fun o => match o with
      | none => (0 : ℕ)
      | some x => if x.val = 2 then 1 else 2)

private theorem first : market.ValidBatch ∅ {0} := by
  simp [MathEconLib.Choice.mem_maximizers, Set.mem_ofPred_eq,
    Subtype.forall, Fin.forall_fin_succ, ValidBatch, Admissible, Unheld,
    holdings, remaining, contractPreference,
    Set.InjOn, Set.Nonempty, Own,
    market, owner, CompletePreference.comap, Preference.comap,
    CompletePreference.ofUtility, CompletePreference.ofPreorder, Preference.ofPreorder, Preference.lt,
    Subtype.exists]

private theorem second : market.ValidBatch {0} {2} := by
  simp [MathEconLib.Choice.mem_maximizers, Set.mem_ofPred_eq,
    Subtype.forall, Fin.forall_fin_succ, ValidBatch, Admissible, Unheld,
    holdings, remaining, contractPreference,
    Set.InjOn, Set.Nonempty, Own,
    market, owner, CompletePreference.comap, Preference.comap,
    CompletePreference.ofUtility, CompletePreference.ofPreorder, Preference.ofPreorder, Preference.lt,
    Bool.exists_bool, Subtype.exists]

private theorem third : market.ValidBatch ({0} ∪ {2}) {1} := by
  simp [MathEconLib.Choice.mem_maximizers, Set.mem_ofPred_eq,
    Subtype.forall, Fin.forall_fin_succ, ValidBatch, Admissible, Unheld,
    holdings, remaining, contractPreference,
    Set.InjOn, Set.Nonempty, Own,
    market, owner, CompletePreference.comap, Preference.comap,
    CompletePreference.ofUtility, CompletePreference.ofPreorder, Preference.ofPreorder, Preference.lt,
    Bool.exists_bool, Subtype.exists]

private theorem together : market.ValidBatch ∅ {0, 1} := by
  simp [MathEconLib.Choice.mem_maximizers, Set.mem_ofPred_eq,
    Subtype.forall, Fin.forall_fin_succ, ValidBatch, Admissible, Unheld,
    holdings, remaining, contractPreference,
    Set.InjOn, Set.Nonempty, Own,
    market, owner, CompletePreference.comap, Preference.comap,
    CompletePreference.ofUtility, CompletePreference.ofPreorder, Preference.ofPreorder, Preference.lt,
    Subtype.exists]

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
  simp [Unheld, holdings, remaining, Eligible, Terminal, Set.Nonempty, Own,
    market, owner, offers, CompletePreference.comap, Preference.comap,
    CompletePreference.ofUtility, CompletePreference.ofPreorder, Preference.ofPreorder, Preference.lt,
    Bool.exists_bool, Subtype.exists, Fin.forall_fin_succ,
    Fin.exists_fin_succ]

/-- Recalling the first proposal produces two held contracts for its proposer. -/
theorem sequential_holdings :
    market.holdings (offers [{1}, {2}, {0}]) = {0, 1, 2} := by
  ext x
  fin_cases x <;> simp [holdings, offers, market, Bool.exists_bool]

/-- Batching the first offers prevents the second contract of proposer false from being offered. -/
theorem simultaneous_holdings :
    market.holdings (offers [{0, 1}]) = {0, 1} := by
  ext x
  fin_cases x <;> simp [holdings, offers, market, Bool.exists_bool]

/-- A concrete application of the generic productive-round bound. -/
example : ([{1}, {2}, {0}] : List (Set (Fin 3))).length ≤ Nat.card (Fin 3) :=
  sequential_run.length_le_card market

/-- Finite policy execution yields a terminal outcome through the public matching umbrella. -/
example (priority : LinearOrder (Fin 3)) :
    market.Outcome (market.rawOutcome (liftStatePolicy (market.fixedOrder priority))) :=
  market.rawOutcome_isOutcome ((market.fixedOrder_valid priority).lift market)

/-- Empty contracts exhaust immediately, with no assumption on receiving choices. -/
example (P : Process Bool Bool Empty) : P.Terminal ∅ := by
  intro s hs
  obtain ⟨x, _⟩ := hs.2
  exact nomatch x.val

end MathEconLibTest.Matching.CumulativeOffer
