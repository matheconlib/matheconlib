/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.GameTheory.Equilibrium.Choice
public import MathEconLib.GameTheory.Strategic.Basic

/-!
# Strategic best responses

Best responses hold opponents' actions fixed and retain every action attaining the greatest
payoff. The correspondence can be empty when no action attains a greatest payoff.

## Main definitions

* `StrategicGame.bestResponses`: value-induced choice over a player's actions.

## Main statements

* `StrategicGame.mem_bestResponses`: comparison against every unilateral action change.
* `StrategicGame.isNash_iff_mem_bestResponses`: Nash equilibrium as best-response membership.
-/

@[expose] public section

namespace MathEconLib.GameTheory.StrategicGame

open Choice

variable {I V : Type*} {A : I → Type*} [DecidableEq I]

private theorem nashMenu_eq_range_update (G : StrategicGame I A V) (i : I) (a : ∀ j, A j) :
    insert a {t | G.nashProblem.deviation i a t} = Set.range (Function.update a i) := by
  have h : {t | G.nashProblem.deviation i a t} = Set.range (Function.update a i) :=
    Set.ext fun _ ↦ exists_congr fun _ ↦ eq_comm
  rw [h]
  exact Set.insert_eq_of_mem ⟨a i, by simp⟩

variable [Preorder V]

/-- All actions attaining the greatest payoff against the supplied opponents' actions. -/
def bestResponses (G : StrategicGame I A V) (i : I) (a : ∀ j, A j) : Set (A i) :=
  ChoiceFunction.ofValue (fun s ↦ G.payoff i (Function.update a i s)) Set.univ

/-- A best response gives payoff weakly above every action against the same opponents. -/
@[simp] theorem mem_bestResponses (G : StrategicGame I A V) (i : I) (a : ∀ j, A j)
    (s : A i) :
    s ∈ G.bestResponses i a ↔
      ∀ t, G.payoff i (Function.update a i t) ≤ G.payoff i (Function.update a i s) := by
  simp [bestResponses, isMaxOn_univ_iff]

/-- A profile is Nash exactly when every player's incumbent action is a best response. -/
theorem isNash_iff_mem_bestResponses (G : StrategicGame I A V) (a : ∀ i, A i) :
    G.IsNash a ↔ ∀ i, a i ∈ G.bestResponses i a := by
  change G.nashProblem.IsEquilibrium a ↔ _
  rw [G.nashProblem.isEquilibrium_iff_mem_ofValue]
  apply forall_congr'
  intro i
  rw [nashMenu_eq_range_update, ChoiceFunction.mem_ofValue, isMaxOn_iff, mem_bestResponses]
  constructor
  · intro h t
    simpa only [nashProblem, Function.update_eq_self] using h.2 _ ⟨t, rfl⟩
  · intro h
    refine ⟨⟨a i, by simp⟩, ?_⟩
    rintro _ ⟨t, rfl⟩
    simpa only [nashProblem, Function.update_eq_self] using h t

/-- Changing the player's incumbent action leaves the best-response set unchanged. -/
@[simp] theorem bestResponses_update (G : StrategicGame I A V) (i : I) (a : ∀ j, A j)
    (s : A i) : G.bestResponses i (Function.update a i s) = G.bestResponses i a :=
  Set.ext fun t ↦ by simp [Function.update_idem]

end MathEconLib.GameTheory.StrategicGame
