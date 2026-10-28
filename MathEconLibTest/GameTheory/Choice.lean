/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib
import MathEconLibExamples

/-!
# Best-response bridges through public imports

Pin the game and equilibrium-problem interfaces, including a nonreflexive deviation relation.
Apply the canonical matching-pennies development to all mixed actions and the explicit biased
action, rather than constructing another game or expected-payoff implementation.
-/

namespace MathEconLibTest.GameTheory.Choice

open MathEconLib.Choice MathEconLib.GameTheory MathEconLib.Probability
open MathEconLibExamples.GameTheory.MatchingPennies

example {I : Type*} {A : I → Type*} {V : Type*} [Preorder V] [DecidableEq I]
    (G : StrategicGame I A V) (i : I) (a : ∀ j, A j) :
    G.bestResponses i a =
      ChoiceFunction.ofValue (fun s ↦ G.payoff i (Function.update a i s)) Set.univ := rfl

example {I : Type*} {A : I → Type*} {V : Type*} [Preorder V] [DecidableEq I]
    (G : StrategicGame I A V) (a : ∀ j, A j) :
    G.IsNash a ↔ ∀ i, a i ∈ G.bestResponses i a :=
  StrategicGame.isNash_iff_mem_bestResponses G a

example {I S V : Type*} [Preorder V] (P : EquilibriumProblem S I V) (s : S) :
    P.IsEquilibrium s ↔
      ∀ i, s ∈ ChoiceFunction.ofValue (P.value i) (insert s {t | P.deviation i s t}) :=
  P.isEquilibrium_iff_mem_ofValue s

private def noDeviations : EquilibriumProblem ℕ Unit ℕ where
  deviation _ _ _ := False
  value _ := id

/-- Staying put need not be admitted: equilibrium still gives incumbent choice membership. -/
example : ∀ i, 0 ∈ ChoiceFunction.ofValue (noDeviations.value i)
    (insert 0 {t | noDeviations.deviation i 0 t}) :=
  (noDeviations.isEquilibrium_iff_mem_ofValue 0).mp fun _ _ h ↦ h.elim

/-- Omitting the incumbent would incorrectly exclude this equilibrium from the empty menu. -/
example : 0 ∉ ChoiceFunction.ofValue (noDeviations.value ())
    {t | noDeviations.deviation () 0 t} :=
  fun h ↦ h.1.elim

example (i : Fin 2) (τ : FinDist (Fin 2)) :
    τ ∈ matchingPennies.finiteMixedExtension.bestResponses i uniformProfile := by
  simp [bestResponses_uniform_eq_univ]

example (i : Fin 2) (σ : FinDist (Fin 2)) :
    biasedAction ∈ matchingPennies.finiteMixedExtension.bestResponses i
      (Function.update uniformProfile i σ) := by
  simp only [bestResponses_uniform_opponent_eq_univ, Set.mem_univ]

example : biasedAction heads = 3 / 4 ∧ biasedAction tails = 1 / 4 :=
  biasedAction_probabilities

example : matchingPennies.IsFiniteMixedNash uniformProfile := uniform_isNash_of_bestResponses

#print axioms StrategicGame.bestResponses
#print axioms StrategicGame.mem_bestResponses
#print axioms StrategicGame.isNash_iff_mem_bestResponses
#print axioms StrategicGame.bestResponses_update
#print axioms EquilibriumProblem.isEquilibrium_iff_mem_ofValue
#print axioms bestResponses_uniform_eq_univ
#print axioms bestResponses_uniform_opponent_eq_univ
#print axioms biasedAction_probabilities
#print axioms biasedAction_mem_bestResponses
#print axioms uniform_isNash_of_bestResponses

end MathEconLibTest.GameTheory.Choice
