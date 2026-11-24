/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib
import MathEconLibExamples

/-!
# Matching-pennies best-response checks

Apply the canonical matching-pennies development to all mixed actions and the explicit biased
action, rather than constructing another game or expected-payoff implementation.
-/

namespace MathEconLibTest.GameTheory.MatchingPenniesBestResponses

open MathEconLib.GameTheory MathEconLib.Probability
open MathEconLibExamples.GameTheory.MatchingPennies

example (i : Fin 2) (τ : FinDist (Fin 2)) :
    τ ∈ matchingPennies.finiteMixedExtension.bestResponses i uniformProfile := by
  simp [bestResponses_uniform_eq_univ]

example (i : Fin 2) (σ : FinDist (Fin 2)) :
    biasedAction ∈ matchingPennies.finiteMixedExtension.bestResponses i
      (Function.update uniformProfile i σ) := by
  simp only [StrategicGame.bestResponses_update, bestResponses_uniform_eq_univ, Set.mem_univ]

example : biasedAction heads = 3 / 4 ∧ biasedAction tails = 1 / 4 :=
  biasedAction_probabilities

example : matchingPennies.IsFiniteMixedNash uniformProfile := uniform_isNash_of_bestResponses

#print axioms bestResponses_uniform_eq_univ
#print axioms biasedAction_probabilities
#print axioms biasedAction_mem_bestResponses
#print axioms uniform_isNash_of_bestResponses

end MathEconLibTest.GameTheory.MatchingPenniesBestResponses
