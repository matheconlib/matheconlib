/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.Value
public import MathEconLib.GameTheory.Strategic.Basic

/-!
# Best responses as value-induced choice

Best responses hold opponents' actions fixed and retain every action attaining the greatest
payoff. Nash equilibrium means that each incumbent action belongs to this choice. No existence,
uniqueness, finiteness, or completeness assumption is built into the correspondence.

For a general equilibrium problem, each deviator chooses from the incumbent state together with
the states admitted by its deviation relation. Including the incumbent makes the characterization
valid even when staying put is not an admissible deviation. With partially ordered payoffs these
are greatest feasible choices; merely excluding strict improvements is weaker.

## Main definitions

* `StrategicGame.bestResponses`: value-induced choice over a player's actions.

## Main statements

* `StrategicGame.mem_bestResponses`: comparison against every unilateral action change.
* `StrategicGame.isNash_iff_mem_bestResponses`: Nash equilibrium as best-response membership.
* `EquilibriumProblem.isEquilibrium_iff_mem_ofValue`: equilibrium as choice among the incumbent
  and allowed deviations.
-/

@[expose] public section

namespace MathEconLib.GameTheory

open Choice

variable {I S V : Type*} {A : I → Type*} [Preorder V]

/-- Equilibrium is greatest-value choice from the incumbent and the allowed deviations.
No reflexivity of the deviation relation is required. -/
theorem EquilibriumProblem.isEquilibrium_iff_mem_ofValue (P : EquilibriumProblem S I V) (s : S) :
    P.IsEquilibrium s ↔
      ∀ i, s ∈ ChoiceFunction.ofValue (P.value i) (insert s {t | P.deviation i s t}) := by
  simp [ChoiceFunction.mem_ofValue, isMaxOn_iff, EquilibriumProblem.isEquilibrium_iff]

namespace StrategicGame

variable [DecidableEq I]

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
  simp [isNash_iff]

/-- Changing the player's incumbent action leaves the best-response set unchanged. -/
@[simp] theorem bestResponses_update (G : StrategicGame I A V) (i : I) (a : ∀ j, A j)
    (s : A i) : G.bestResponses i (Function.update a i s) = G.bestResponses i a :=
  Set.ext fun t ↦ by simp [Function.update_idem]

end StrategicGame

end MathEconLib.GameTheory
